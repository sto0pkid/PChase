dbg(dummy).
% dbg(rule_match).
% dbg(item_match).
dbg(pchase).
dbg(Type, Format, Args) :-
	(
	   dbg(Type)
	-> (
		format(atom(A), Format, Args),
		format("~w: ~w~n", [Type, A])
	   )
	; true
	).

subst_unify(X,Y) :- var(X), !, X = Y.
subst_unify(bnode(X),bnode(Y)) :- X == Y.
subst_unify(const(X),const(Y)) :- X == Y.

subst_unify([],[]) :- !.
subst_unify([T1|T1s],[T2|T2s]) :-
	subst_unify(T1, T2),
	subst_unify(T1s, T2s).

hom_unify(X,Y,_,_) :- var(X), !, X = Y.
hom_unify(bnode(X),Y,Bindings,New_Bindings) :-
	(
		member([bnode(X),Binding],Bindings)
	->	Binding = Y
	;	New_Bindings = [[bnode(X),Y] | Bindings]
	).
hom_unify(const(X),const(Y),_,_) :- X == Y.

hom_unify([],[],_,_) :- !.
hom_unify([T1|T1s],[T2|T2s],Bindings,_) :-
	dbg(hom_unify, "`~w` with `~w`", [T1, T2]),
	hom_unify(T1, T2, Bindings, Next_Bindings),
	hom_unify(T1s, T2s, Next_Bindings, _).

new_check(Head,[]) :- !, debug(new_check, "~w: []", [Head, []]).
new_check(Head,[Fact|Facts]) :-
	dbg(new_check, "~w: ~w", [Head, Fact]),
	\+hom_unify(Head,Fact,[],_),
	new_check(Head,Facts),
	dbg(new_check, "Succeed",[]).

item_match(Item, Facts) :-
	member(Fact, Facts),
	dbg(item_match, "~nItem: ~w~nFact: ~w~n", [Item, Fact]),
	subst_unify(Item, Fact).

rule_match([],_) :- !.
rule_match([Item|Body], Facts) :-
	dbg(rule_match, "Item: ~w", [Item]),
	item_match(Item, Facts),
	rule_match(Body, Facts).

gen_bnodes([]) :- !.
gen_bnodes([X|Rest]) :-
	(
	   var(X)
	-> (
		gensym(b,Fresh),
		X = bnode(Fresh)
	   )
	;  true
	),
	gen_bnodes(Rest).


run_rule(Rule, Facts, Output) :-
	copy_term_nat(Rule, ':-'(Head,Body)),
	findall(
		Head,
		(
			rule_match(Body,Facts),
			new_check(Head,Facts),
			gen_bnodes(Head)
		),
		Output		
	).

round([],_,[]).
round([Rule|Rules], Facts, New_Facts) :-
	run_rule(Rule, Facts, Output),
	round(Rules, Facts, Next_Facts),
	append(Output, Next_Facts, New_Facts).



pchase(Rules, Facts, Step, Output) :-
	Next_Step is Step + 1,
	dbg(pchase, "Step: ~w~n", [Next_Step]),
	Step < 5,
	round(Rules, Facts, New_Facts),
	append(Facts, New_Facts, Next_Facts),
	dbg(pchase, "New facts: ~w~n", [New_Facts]),
	(
		New_Facts = []
	->	Output = Next_Facts
	;	pchase(Rules,Next_Facts,Next_Step,Output)
	).










% 
% TEST DATA
%


test_rule_body_1([
	[_,X,const(a),const(nat)],
	[_,X,const(suc),_]
]).
test_facts_1(
	[
		[1, const(0), const(a), const(nat)],
		[2, const(0), const(suc), bnode(b1)],
		[3, bnode(b1), const(a), const(nat)],
		[4, bnode(b1), const(suc), bnode(b2)],
		[5, bnode(b2), const(a), const(nat)]
	]
).

test_rule_1(':-'(
	[_,X,const(foo),_],
	[
		[_,X,const(a),const(nat)],
		[_,X,const(suc),_]
	])
).


test_facts_2(
	[
		[const(0), const(a), const(nat)],
		[const(0), const(suc), bnode(b1)],
		[bnode(b1), const(a), const(nat)],
		[bnode(b1), const(suc), bnode(b2)],
		[bnode(b2), const(a), const(nat)]
	]

).

test_rule_2(':-'(
	[Y,const(a),const(nat)],
	[
		[X,const(a),const(nat)],
		[X,const(suc),Y]
	])
).


test_kb_1(
	[
		':-'(
			[Y,const(a),const(nat)],
			[
				[_,const(suc),Y]
			]
		),
		':-'(
			[X,const(suc),_],
			[
				[X,const(a),const(nat)]
			]
		)
	]
).

test_facts_3(
	[
		[const(0),const(a),const(nat)]
	]
).

%
%  TEST ASSERTIONS
%


test1() :-
	Head = [const(a),const(p),bnode(_)],
	Facts = [[const(a),const(r),const(a)],[const(a),const(p),const(b)]],
	\+new_check(Head,Facts).

test2() :-
	Head = [const(a),const(p),bnode(_)],
	Facts = [[const(a),const(r),const(a)],[const(a),const(r),const(b)]],
	new_check(Head, Facts).

test3() :-
	test_rule_body_1(Body),
	test_facts_1(Facts),
	rule_match(Body,Facts),
	format("result: ~w~n", [Body]).

test4() :-
	test_rule_1(Rule),
	test_facts_1(Facts),
	format("Rule: ~w~n", [Rule]),
	format("Facts: ~w~n", [Facts]),
	run_rule(Rule, Facts, Results),
	format("Results: ~w~n", [Results]).

test5() :-
	test_rule_2(Rule),
	test_facts_2(Facts),
	format("Rule: ~w~n", [Rule]),
	format("Facts: ~w~n", [Facts]),
	run_rule(Rule, Facts, Results),
	format("Results: ~w~n", [Results]).


test6() :-
	test_kb_1(KB),
	test_facts_2(Facts),
	pchase(KB,Facts,0,Output),
	format("Results: ~w~n", [Output]).

test_kb(KBGen, FactsGen) :-
	call(KBGen, KB),
	call(FactsGen, Facts),
	pchase(KB, Facts, 0, Output),
	format("Results: ~w~n", [Output]).

test7() :-
	test_kb(test_kb_1, test_facts_3).
