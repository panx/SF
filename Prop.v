(** * Prop: Propositions and Evidence *)

Require Export MoreCoq.

(** In previous chapters, we have seen many examples of factual
    claims (_propositions_) and ways of presenting evidence of their
    truth (_proofs_).  In particular, we have worked extensively with
    _equality propositions_ of the form [e1 = e2], with
    implications ([P -> Q]), and with quantified propositions 
    ([forall x, P]).

    In this chapter we take a deeper look at the way propositions are
    expressed in Coq and at the structure of the logical evidence that
    we construct when we carry out proofs.  

    Some of the concepts in this chapter may seem a bit abstract on a
    first encounter.  We've included a _lot_ of exercises, most of
    which should be quite approachable even if you're still working on
    understanding the details of the text.  Try to work as many of
    them as you can, especially the one-starred exercises. 

*)
(* ##################################################### *)
(** * Inductively Defined Propositions *)

(** This chapter will take us on a first tour of the
    propositional (logical) side of Coq.  As a running example, let's
    define a simple property of natural numbers -- we'll call it
    "[beautiful]." *)

(** Informally, a number is [beautiful] if it is [0], [3], [5], or the
    sum of two [beautiful] numbers.  

    More pedantically, we can define [beautiful] numbers by giving four
    rules:

       - Rule [b_0]: The number [0] is [beautiful].
       - Rule [b_3]: The number [3] is [beautiful]. 
       - Rule [b_5]: The number [5] is [beautiful]. 
       - Rule [b_sum]: If [n] and [m] are both [beautiful], then so is
         their sum. *)

(** We will see many definitions like this one during the rest
    of the course, and for purposes of informal discussions, it is
    helpful to have a lightweight notation that makes them easy to
    read and write.  _Inference rules_ are one such notation: *)
(**
                              -----------                               (b_0)
                              beautiful 0
                              
                              ------------                              (b_3)
                              beautiful 3

                              ------------                              (b_5)
                              beautiful 5    

                       beautiful n     beautiful m
                       ---------------------------                      (b_sum)
                              beautiful (n+m)   
*)

(** Each of the textual rules above is reformatted here as an
    inference rule; the intended reading is that, if the _premises_
    above the line all hold, then the _conclusion_ below the line
    follows.  For example, the rule [b_sum] says that, if [n] and [m]
    are both [beautiful] numbers, then it follows that [n+m] is
    [beautiful] too.  The rules with no premises above the line are
    called _axioms_.

    These rules _define_ the property [beautiful].  That is, if we
    want to convince someone that some particular number is [beautiful],
    our argument must be based on these rules.  For a simple example,
    suppose we claim that the number [5] is [beautiful].  To support
    this claim, we just need to point out that rule [b_5] says so.
    Or, if we want to claim that [8] is [beautiful], we can support our
    claim by first observing that [3] and [5] are both [beautiful] (by
    rules [b_3] and [b_5]) and then pointing out that their sum, [8],
    is therefore [beautiful] by rule [b_sum].  This argument can be
    expressed graphically with the following _proof tree_: *)
(**
         ----------- (b_3)   ----------- (b_5)
         beautiful 3         beautiful 5
         ------------------------------- (b_sum)
                   beautiful 8   
    Of course, there are other ways of using these rules to argue that
    [8] is [beautiful], for instance:
         ----------- (b_5)   ----------- (b_3)
         beautiful 5         beautiful 3
         ------------------------------- (b_sum)
                   beautiful 8   
*)

(** **** Exercise: 1 star (varieties_of_beauty) *)
(** How many different ways are there to show that [8] is [beautiful]? *)

(* infinitly many *)
(** [] *)

(** In Coq, we can express the definition of [beautiful] as
    follows: *)

Inductive beautiful : nat -> Prop :=
|b_0   : beautiful 0
| b_3   : beautiful 3
| b_5   : beautiful 5
| b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n+m).

(** The first line declares that [beautiful] is a proposition -- or,
    more formally, a family of propositions "indexed by" natural
    numbers.  (That is, for each number [n], the claim that "[n] is
    [beautiful]" is a proposition.)  Such a family of propositions is
    often called a _property_ of numbers.  Each of the remaining lines
    embodies one of the rules for [beautiful] numbers.

    We can use Coq's tactic scripting facility to assemble proofs that
    particular numbers are [beautiful].  *)

Theorem three_is_beautiful: beautiful 3.
Proof.
   (* This simply follows from the axiom [b_3]. *)
   apply b_3.
Qed.

Theorem eight_is_beautiful: beautiful 8.
Proof.
   (* First we use the rule [b_sum], telling Coq how to
      instantiate [n] and [m]. *)
   apply b_sum with (n:=3) (m:=5).
   (* To solve the subgoals generated by [b_sum], we must provide
      evidence of [beautiful 3] and [beautiful 5]. Fortunately we
      have axioms for both. *)
   apply b_3.
   apply b_5.
Qed.

(* ##################################################### *)
(** * Proof Objects *)

(** Look again at the formal definition of the [beautiful]
    property.  The opening keyword, [Inductive], has been used up to
    this point to declare new types of _data_, such as numbers and
    lists.  Does this interpretation also make sense for the Inductive
    definition of [beautiful]?  That is, can we view evidence of
    beauty as some kind of data structure? Yes, we can!

    The trick is to introduce an alternative pronunciation of "[:]".
    Instead of "has type," we can also say "is a proof of."  For
    example, the second line in the definition of [beautiful] declares
    that [b_0 : beautiful 0].  Instead of "[b_0] has type 
    [beautiful 0]," we can say that "[b_0] is a proof of [beautiful 0]."
    Similarly for [b_3] and [b_5]. *)

(** This pun between types and propositions (between [:] as "has type"
    and [:] as "is a proof of" or "is evidence for") is called the
    _Curry-Howard correspondence_.  It proposes a deep connection
    between the world of logic and the world of computation.
<<
                 propositions  ~  types
                 proofs        ~  data values
>>
    Many useful insights follow from this connection.  To begin with, it
    gives us a natural interpretation of the type of [b_sum] constructor: *)

Check b_sum.
(* ===> b_sum : forall n m, 
                  beautiful n -> 
                  beautiful m -> 
                  beautiful (n+m) *)

(** This can be read "[b_sum] is a constructor that takes four
    arguments -- two numbers, [n] and [m], and two values, of types
    [beautiful n] and [beautiful m] -- and yields evidence for the
    proposition [beautiful (n+m)]." *)

(** In view of this, we might wonder whether we can write an
    expression of type [beautiful 8] by applying [b_sum] to
    appropriate arguments.  Indeed, we can: *)

Check (b_sum 3 5 b_3 b_5).  
(* ===> beautiful (3 + 5) *)

(** The expression [b_sum 3 5 b_3 b_5] can be thought of as
    instantiating the parameterized constructor [b_sum] with the
    specific arguments [3] [5] and the corresponding proof objects for
    its premises [beautiful 3] and [beautiful 5] (Coq is smart enough
    to figure out that 3+5=8).  Alternatively, we can think of [b_sum]
    as a primitive "evidence constructor" that, when applied to two
    particular numbers, wants to be further applied to evidence that
    those two numbers are beautiful; its type, 
[[  
    forall n m, beautiful n -> beautiful m -> beautiful (n+m),
    expresses this functionality, in the same way that the polymorphic
    type [forall X, list X] in the previous chapter expressed the fact
    that the constructor [nil] can be thought of as a function from
    types to empty lists with elements of that type. *)

(** This gives us an alternative way to write the proof that [8] is
    beautiful: *)

Theorem eight_is_beautiful': beautiful 8.
Proof.
   apply (b_sum 3 5 b_3 b_5).
Qed.

(** Notice that we're using [apply] here in a new way: instead of just
    supplying the _name_ of a hypothesis or previously proved theorem
    whose type matches the current goal, we are supplying an
    _expression_ that directly builds evidence with the required
    type. *)

(* ##################################################### *)
(** ** Proof Scripts and Proof Objects *)

(** These proof objects lie at the core of how Coq operates. 

    When Coq is following a proof script, what is happening internally
    is that it is gradually constructing a proof object -- a term
    whose type is the proposition being proved.  The tactics between
    the [Proof] command and the [Qed] instruct Coq how to build up a
    term of the required type.  To see this process in action, let's
    use the [Show Proof] command to display the current state of the
    proof tree at various points in the following tactic proof. *)

Theorem eight_is_beautiful'': beautiful 8.
Proof.
   Show Proof.
   apply b_sum with (n:=3) (m:=5).
   Show Proof.
   apply b_3.
   Show Proof.
   apply b_5.
   Show Proof.
Qed.

(** At any given moment, Coq has constructed a term with some
    "holes" (indicated by [?1], [?2], and so on), and it knows what
    type of evidence is needed at each hole.  In the [Show Proof]
    output, lines of the form [?1 -> beautiful n] record these
    requirements.  (The [->] here has nothing to do with either
    implication or function types -- it is just an unfortunate choice
    of concrete syntax for the output!)  

    Each of the holes corresponds to a subgoal, and the proof is
    finished when there are no more subgoals.  At this point, the
    [Theorem] command gives a name to the evidence we've built and
    stores it in the global context. *)

(** Tactic proofs are useful and convenient, but they are not
    essential: in principle, we can always construct the required
    evidence by hand.  Indeed, we don't even need the [Theorem]
    command: we can instead use [Definition] to directly give a global
    name to a piece of evidence. *)

Definition eight_is_beautiful''' : beautiful 8 :=
  b_sum 3 5 b_3 b_5.

(** All these different ways of building the proof lead to exactly the
    same evidence being saved in the global environment. *)

Print eight_is_beautiful.
(* ===> eight_is_beautiful    = b_sum 3 5 b_3 b_5 : beautiful 8 *)
Print eight_is_beautiful'.
(* ===> eight_is_beautiful'   = b_sum 3 5 b_3 b_5 : beautiful 8 *)
Print eight_is_beautiful''.
(* ===> eight_is_beautiful''  = b_sum 3 5 b_3 b_5 : beautiful 8 *)
Print eight_is_beautiful'''.
(* ===> eight_is_beautiful''' = b_sum 3 5 b_3 b_5 : beautiful 8 *)

(** **** Exercise: 1 star (six_is_beautiful) *)
(** Give a tactic proof and a proof object showing that [6] is [beautiful]. *)

Theorem six_is_beautiful :
  beautiful 6.
Proof.
  apply(b_sum 3 3 b_3 b_3).
Qed.

Definition six_is_beautiful' : beautiful 6 :=
  b_sum 3 3 b_3 b_3.
(** [] *)

(** **** Exercise: 1 star (nine_is_beautiful) *)
(** Give a tactic proof and a proof object showing that [9] is [beautiful]. *)

Theorem nine_is_beautiful :
  beautiful 9.
Proof.
  apply(b_sum 3 6 b_3 six_is_beautiful).
Qed.

Definition nine_is_beautiful' : beautiful 9 :=
  b_sum 3 6 b_3 six_is_beautiful.
(** [] *)


(* ##################################################### *)
(** ** Implications and Functions *)

(** In Coq's computational universe (where we've mostly been living
    until this chapter), there are two sorts of values with arrows in
    their types: _constructors_ introduced by [Inductive]-ly defined
    data types, and _functions_.

    Similarly, in Coq's logical universe, there are two ways of giving
    evidence for an implication: constructors introduced by
    [Inductive]-ly defined propositions, and... functions!

    For example, consider this statement: *)

Theorem b_plus3: forall n, beautiful n -> beautiful (3+n).
Proof.
   intros n H.
   apply b_sum.
   apply b_3.
   apply H.
Qed.

(** What is the proof object corresponding to [b_plus3]? 

    We're looking for an expression whose _type_ is [forall n,
    beautiful n -> beautiful (3+n)] -- that is, a _function_ that
    takes two arguments (one number and a piece of evidence) and
    returns a piece of evidence!  Here it is: *)

Definition b_plus3' : forall n, beautiful n -> beautiful (3+n) := 
  fun n => fun H : beautiful n =>
    b_sum 3 n b_3 H.

Check b_plus3'.
(* ===> b_plus3' : forall n, beautiful n -> beautiful (3+n) *)

(** Recall that [fun n => blah] means "the function that, given [n],
    yields [blah]."  Another equivalent way to write this definition is: *)

Definition b_plus3'' (n : nat) (H : beautiful n) : beautiful (3+n) := 
  b_sum 3 n b_3 H.

Check b_plus3''.
(* ===> b_plus3'' : forall n, beautiful n -> beautiful (3+n) *)

(** **** Exercise: 2 stars (b_times2) *)
Theorem b_times2: forall n, beautiful n -> beautiful (2*n).
Proof.
  intros n H. simpl. rewrite plus_0_r.
  apply(b_sum n n H H).
Qed.
(** [] *)
Print b_times2.
Check eq_ind_r.
(** **** Exercise: 3 stars, optional (b_times2') *)
(** Write a proof object corresponding to [b_times2] above *)

Definition b_times2': forall n, beautiful n -> beautiful (2*n) :=
  fun (n : nat) (H : beautiful n) =>
eq_ind_r (fun n0 : nat => beautiful (n + n0)) (b_sum n n H H) (plus_0_r n).

(** **** Exercise: 2 stars (b_timesm) *)
Theorem b_timesm: forall n m, beautiful n -> beautiful (m*n).
Proof.
   intros n m H. induction m as [|m']. 
   compute. apply b_0. rewrite mult_comm. rewrite mSn. rewrite mult_comm.
   apply(b_sum n (m'*n) H IHm').
   Qed.
   
(** [] *)

(* ####################################################### *)
(** ** Induction Over Proof Objects *)

(** Since we use the keyword [Induction] to define primitive
    propositions together with their evidence, we might wonder whether
    there are some sort of induction principles associated with these
    definitions.  Indeed there are, and in this section we'll take a
    look at how they can be used.  *)

(** Besides _constructing_ evidence that numbers are beautiful, we can
    also _reason about_ such evidence. *)

(** The fact that we introduced [beautiful] with an [Inductive]
    declaration tells us not only that the constructors [b_0], [b_3],
    [b_5] and [b_sum] are ways to build evidence, but also that these
    two constructors are the _only_ ways to build evidence that
    numbers are beautiful. *)

(** In other words, if someone gives us evidence [E] for the assertion
    [beautiful n], then we know that [E] must have one of four shapes:

      - [E] is [b_0] (and [n] is [O]),
      - [E] is [b_3] (and [n] is [3]), 
      - [E] is [b_5] (and [n] is [5]), or 
      - [E] is [b_sum n1 n2 E1 E2] (and [n] is [n1+n2], where [E1] is
        evidence that [n1] is beautiful and [E2] is evidence that [n2]
        is beautiful). *)
    
(** This gives rise to an _induction principle_ for proofs -- i.e., we
    can use the [induction] tactic that we have already seen for
    reasoning about inductively defined _data_ to reason about
    inductively defined _evidence_.

    To illustrate this, let's define another property of numbers: *)

Inductive gorgeous : nat -> Prop :=
  g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3+n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5+n).

(** **** Exercise: 1 star (gorgeous_tree) *)
(** Write out the definition of [gorgeous] numbers using inference rule
    notation.
 
(**
                              -----------                               (g_0)
                              gorgeous 0

                             gorgeous n  
                       ---------------------------                   (g_plus3)
                             gorgeous (3+n)   

                             gorgeous n  
                       ---------------------------                   (g_plus5)
                             gorgeous (5+n)   
*)
[]
*)

(** It seems intuitively obvious that, although [gorgeous] and
    [beautiful] are presented using slightly different rules, they are
    actually the same property in the sense that they are true of the
    same numbers.  Indeed, we can prove this. *)

Theorem gorgeous__beautiful : forall n, 
  gorgeous n -> beautiful n.
Proof.
   intros n H.
   induction H as [|n'|n'].
   Case "g_0".
       apply b_0.
   Case "g_plus3". 
       apply b_sum. apply b_3.
       apply IHgorgeous.
   Case "g_plus5".
       apply b_sum. apply b_5. apply IHgorgeous. 
Qed.

(** Notice that the argument proceeds by induction on the _evidence_ [H]! *) 

(** Let's see what happens if we try to prove this by induction on [n]
   instead of induction on the evidence [H]. *)

Theorem gorgeous__beautiful_FAILED : forall n, 
  gorgeous n -> beautiful n.
Proof.
   intros. induction n as [| n'].
   Case "n = 0". apply b_0.
   Case "n = S n'". (* We are stuck! *)
Admitted.

(** The problem here is that doing induction on [n] doesn't yield a
    useful induction hypothesis. Knowing how the property we are
    interested in behaves on the predecessor of [n] doesn't help us
    prove that it holds for [n]. Instead, we would like to be able to
    have induction hypotheses that mention other numbers, such as [n -
    3] and [n - 5]. This is given precisely by the shape of the
    constructors for [gorgeous]. *)



(** **** Exercise: 1 star (gorgeous_plus13) *)
Theorem gorgeous_plus13: forall n, 
  gorgeous n -> gorgeous (13+n).
Proof.
   intros n H. apply g_plus3. apply g_plus5. apply g_plus5. apply H. Qed.
(** [] *)
Print gorgeous_plus13.
(** **** Exercise: 2 stars, optional (gorgeous_plus13_po):
Give the proof object for theorem [gorgeous_plus13] above. *)

Definition gorgeous_plus13_po: forall n, gorgeous n -> gorgeous (13+n):=
   fun (n : nat) (H : gorgeous n) =>
   g_plus3 (S (S (S (S (S (S (S (S (S (S n))))))))))
  (g_plus5 (S (S (S (S (S n))))) (g_plus5 n H)).
(** [] *)

(** **** Exercise: 2 stars (gorgeous_sum) *)
Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
  intros n m h1 h2. induction h1 as [|n'|n'].
  Case "g_0". simpl. apply h2.
  Case "g_plus3". apply g_plus3. apply IHh1.
  Case "g_plus5". apply g_plus5. apply IHh1.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (beautiful__gorgeous) *)
Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
  intros n H. induction H.
  Case "b_0". apply g_0.
  Case "b_3". apply g_plus3. apply g_0.
  Case "b_5". apply g_plus5. apply g_0.
  induction IHbeautiful1. 
    SCase "g_0". apply IHbeautiful2.
    SCase "g_plus3". apply g_plus3. apply IHIHbeautiful1. apply gorgeous__beautiful. apply IHbeautiful1.
    SCase "g_plus5". apply g_plus5. apply IHIHbeautiful1. apply gorgeous__beautiful. apply IHbeautiful1.
  Qed.
  
(** [] *)

(** **** Exercise: 3 stars, optional (b_times2) *)
(** Prove the [g_times2] theorem below without using [gorgeous__beautiful].
    You might find the following helper lemma useful. *)

Lemma helper_g_times2 : forall x y z, x + (z + y)= z + x + y.
Proof.
   intros x y z. rewrite plus_assoc. replace (x+z) with (z+x). reflexivity. rewrite plus_comm. reflexivity. Qed.

Theorem g_times2: forall n, gorgeous n -> gorgeous (2*n).
Proof.
   intros n H. simpl. 
   induction H.
   compute. apply g_0.
   rewrite plus_0_r. rewrite  helper_g_times2. apply g_plus3. apply g_plus3. rewrite plus_0_r in IHgorgeous. apply IHgorgeous.
   rewrite plus_0_r. rewrite helper_g_times2. apply g_plus5. apply g_plus5. rewrite plus_0_r in IHgorgeous. apply IHgorgeous.
  Qed.
(** [] *)


(* ####################################################### *)
(** ** From Boolean Functions to Propositions *)

(** In chapter [Basics] we defined a _function_ [evenb] that tests a
    number for evenness, yielding [true] if so.  We can use this
    function to define the _proposition_ that some number [n] is
    even: *)

Definition even (n:nat) : Prop := 
  evenb n = true.
Check even.

(** That is, we can define "[n] is even" to mean "the function [evenb]
    returns [true] when applied to [n]." *)

(** Another alternative is to define the concept of evenness
    directly.  Instead of going via the [evenb] function ("a number is
    even if a certain computation yields [true]"), we can say what the
    concept of evenness means by giving two different ways of
    presenting _evidence_ that a number is even. *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

(** This definition says that there are two ways to give
    evidence that a number [m] is even.  First, [0] is even, and
    [ev_0] is evidence for this.  Second, if [m = S (S n)] for some
    [n] and we can give evidence [e] that [n] is even, then [m] is
    also even, and [ev_SS n e] is the evidence. *)


(** **** Exercise: 1 star (double_even) *)
(** Construct a tactic proof of the following proposition. *)

Theorem double_even : forall n,
  ev (double n).
Proof.
  intros n.
  induction n as [|n']. 
  simpl. apply ev_0.
  simpl. apply ev_SS. apply IHn'.
  Qed.
(** [] *)
Print double_even.
(** **** Exercise: 4 stars, optional (double_even_pfobj) *)
(** Try to predict what proof object is constructed by the above
    tactic proof.  (Before checking your answer, you'll want to
    strip out any uses of [Case], as these will make the proof
    object look a bit cluttered.) *)
(*fun n : nat =>
 nat_ind (fun n0 : nat => ev (double n0)) (ev_0:ev (double 0))
   (fun (n' : nat) (IHn' : ev (double n')) =>
    ev_SS (double n') IHn':ev (double (S n'))) nfun n. *)

(** ** Discussion: Computational vs. Inductive Definitions *)

(** We have seen that the proposition "[n] is even" can be
    phrased in two different ways -- indirectly, via a boolean testing
    function [evenb], or directly, by inductively describing what
    constitutes evidence for evenness.  These two ways of defining
    evenness are about equally easy to state and work with.  Which we
    choose is basically a question of taste.

    However, for many other properties of interest, the direct
    inductive definition is preferable, since writing a testing
    function may be awkward or even impossible.  

    One such property is [beautiful].  This is a perfectly sensible
    definition of a set of numbers, but we cannot translate its
    definition directly into a Coq Fixpoint (or into a recursive
    function in any other common programming language).  We might be
    able to find a clever way of testing this property using a
    [Fixpoint] (indeed, it is not too hard to find one in this case),
    but in general this could require arbitrarily deep thinking.  In
    fact, if the property we are interested in is uncomputable, then
    we cannot define it as a [Fixpoint] no matter how hard we try,
    because Coq requires that all [Fixpoint]s correspond to
    terminating computations.

    On the other hand, writing an inductive definition of what it
    means to give evidence for the property [beautiful] is
    straightforward. *)


(* ####################################################### *)
(** ** [Inversion] on Evidence *)

(** Besides [induction], we can use the other tactics in our toolkit
    to reason about evidence.  For example, this proof uses [destruct]
    on evidence. *)

Theorem ev_minus2: forall n,
  ev n -> ev (pred (pred n)). 
Proof.
  intros n E.
  destruct E as [| n' E'].
  Case "E = ev_0". simpl. apply ev_0. 
  Case "E = ev_SS n' E'". simpl. apply E'.  Qed.

(** **** Exercise: 1 star, optional (ev_minus2_n) *)
(** What happens if we try to [destruct] on [n] instead of [E]? *)

(* It will get stuck because ev n does not imply ev (S n)*)
(** [] *)

(** **** Exercise: 1 star (ev__even) *)
(** Here is a proof that the inductive definition of evenness implies
    the computational one. *)

Theorem ev__even : forall n,
  ev n -> even n.
Proof.
  intros n E. induction E as [| n' E'].
  Case "E = ev_0". 
    unfold even. reflexivity.
  Case "E = ev_SS n' E'".  
    unfold even. apply IHE'.  
Qed.

(** Could this proof also be carried out by induction on [n] instead
    of [E]?  If not, why not? *)

(* This proof could not be carried out by induction on [n]. Because ev does not hold on consecutive n's*)
(** [] *)

(** The induction principle for inductively defined propositions does
    not follow quite the same form as that of inductively defined
    sets.  For now, you can take the intuitive view that induction on
    evidence [ev n] is similar to induction on [n], but restricts our
    attention to only those numbers for which evidence [ev n] could be
    generated.  We'll look at the induction principle of [ev] in more
    depth below, to explain what's really going on. *)

(** **** Exercise: 1 star (l_fails) *)
(** The following proof attempt will not succeed.
     Theorem l : forall n,
       ev n.
     Proof.
       intros n. induction n.
         Case "O". simpl. apply ev_0.
         Case "S".
           ...
   Briefly explain why.
 
(* Induction n would only succed when all ev n is true.*)
*)
(** [] *)

(** **** Exercise: 2 stars (ev_sum) *)
(** Here's another exercise requiring induction. *)

Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof. 
  intros n m h1 h2. induction h1. 
  simpl. apply h2.
  simpl. apply ev_SS. apply IHh1.
  Qed.
(** [] *)

(** Another situation where we want to analyze evidence for evenness
    is when proving that, if [n+2] is even, then [n] is. *)

(** Our first idea might be to use [destruct] for this kind of case
    analysis: *)

Theorem SSev_ev_firsttry : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. 
  destruct E as [| n' E'].
  (* Stuck: [destruct] gives us an unprovable subgoal here! *)
Admitted.

(** In the first sub-goal, we've lost the information that [n] is [0].
    We could have used [remember], but then we still need [inversion]
    on both cases. *)

Theorem SSev_ev_secondtry : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. remember (S (S n)) as n2.
  destruct E as [| n' E'].
  Case "n = 0". inversion Heqn2.
  Case "n = S n'". inversion Heqn2. rewrite <- H0. apply E'.
Qed.

(** There is a much simpler way to do this. We can use
    [inversion] directly on the inductively defined proposition
    [ev (S (S n))]. *)

Theorem SSev__even : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. inversion E as [| n' E']. apply E'. Qed.

(** This use of [inversion] may seem a bit mysterious at first.
    Until now, we've only used [inversion] on equality
    propositions, to utilize injectivity of constructors or to
    discriminate between different constructors.  But we see here
    that [inversion] can also be applied to analyzing evidence
    for inductively defined propositions.

    Here's how [inversion] works in general.  Suppose the name
    [I] refers to an assumption [P] in the current context, where
    [P] has been defined by an [Inductive] declaration.  Then,
    for each of the constructors of [P], [inversion I] generates
    a subgoal in which [I] has been replaced by the exact,
    specific conditions under which this constructor could have
    been used to prove [P].  Some of these subgoals will be
    self-contradictory; [inversion] throws these away.  The ones
    that are left represent the cases that must be proved to
    establish the original goal.

    In this particular case, the [inversion] analyzed the construction
    [ev (S (S n))], determined that this could only have been
    constructed using [ev_SS], and generated a new subgoal with the
    arguments of that constructor as new hypotheses.  (It also
    produced an auxiliary equality, which happens to be useless here.)
    We'll begin exploring this more general behavior of inversion in
    what follows. *)

(** **** Exercise: 1 star (inversion_practice) *)
Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n h. inversion h. inversion H0. apply H2. Qed.

(** The [inversion] tactic can also be used to derive goals by showing
    the absurdity of a hypothesis. *)

Theorem even5_nonsense : 
  ev 5 -> 2 + 2 = 9.
Proof.
  intros h. apply ev__even in h. inversion h. Qed.
(** [] *)

(** We can generally use [inversion] on inductive propositions.
    This illustrates that in general, we get one case for each
    possible constructor.  Again, we also get some auxiliary
    equalities that are rewritten in the goal but not in the other
    hypotheses. *)

Theorem ev_minus2': forall n,
  ev n -> ev (pred (pred n)). 
Proof.
  intros n E. inversion E as [| n' E']. 
  Case "E = ev_0". simpl. apply ev_0. 
  Case "E = ev_SS n' E'". simpl. apply E'.  Qed.

(** **** Exercise: 3 stars, advanced (ev_ev__ev) *)
(** Finding the appropriate thing to do induction on is a
    bit tricky here: *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, optional (ev_plus_plus) *)
(** Here's an exercise that just requires applying existing lemmas.  No
    induction or even case analysis is needed, but some of the rewriting
    may be tedious.  You'll want the [replace] tactic used for [plus_swap']
    in Basics.v *)
Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof. Admitted.
(** [] *)

(* ####################################################### *)
(** ** Building Proof Objects Incrementally (Optional) *)

(** As you probably noticed while solving the exercises earlier in the
    chapter, constructing proof objects is more involved than
    constructing the corresponding tactic proofs. Fortunately, there
    is a bit of syntactic sugar that we've already introduced to help
    in the construction: the [admit] term, which we've sometimes used
    to force Coq into accepting incomplete exercies. As an example,
    let's walk through the process of constructing a proof object
    demonstrating the beauty of [16]. *)

Definition b_16_atmpt_1 : beautiful 16 := admit.

(** Maybe we can use [b_sum] to construct a term of type [beautiful 16]?
    Recall that [b_sum] is of type

    forall n m : nat, beautiful n -> beautiful m -> beautiful (n + m)

    If we can demonstrate the beauty of [5] and [11], we should
    be done. *)

Definition b_16_atmpt_2 : beautiful 16 := b_sum 5 11 admit admit.

(** In the attempt above, we've omitted the proofs of the propositions
    that [5] and [11] are beautiful. But the first of these is already
    axiomatized in [b_5]: *)

Definition b_16_atmpt_3 : beautiful 16 := b_sum 5 11 b_5 admit.

(** What remains is to show that [11] is beautiful. We repeat the
    procedure: *)

Definition b_16_atmpt_4 : beautiful 16 :=
  b_sum 5 11 b_5 (b_sum 5 6 admit admit).

Definition b_16_atmpt_5 : beautiful 16 :=
  b_sum 5 11 b_5 (b_sum 5 6 b_5 admit).

Definition b_16_atmpt_6 : beautiful 16 :=
  b_sum 5 11 b_5 (b_sum 5 6 b_5 (b_sum 3 3 admit admit)).

(** And finally, we can complete the proof object: *)

Definition b_16 : beautiful 16 :=
  b_sum 5 11 b_5 (b_sum 5 6 b_5 (b_sum 3 3 b_3 b_3)).

(** To recap, we've been guided by an informal proof that we have in
    our minds, and we check the high level details before completing
    the intricacies of the proof. The [admit] term allows us to do
    this. *)

(* ####################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 4 stars (palindromes) *)
(** A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor
    c : forall l, l = rev l -> pal l
      may seem obvious, but will not work very well.)
 
    - Prove that 
       forall l, pal (l ++ rev l).
    - Prove that 
       forall l, pal l -> l = rev l.
*)

Inductive pal {X : Type} : list X -> Prop :=
| pal_nil : pal []
| pal_one : forall x, pal [x]
| pal_more : forall x l, pal l -> pal ( cons x (snoc l x)).

Require Export Poly.

Theorem pal_l_revl: forall {X:Type} (l: list X), pal (l ++ rev l).
Proof. intros X l. induction l. 
  simpl. apply pal_nil. simpl. rewrite <- snoc_with_append. apply pal_more. apply IHl.
Qed.

Theorem pal_eq_revl: forall {X:Type} (l:list X), pal l -> l=rev l.
Proof. intros X l h. induction h.
  reflexivity.
  reflexivity.
  simpl. rewrite rev_snoc. simpl. rewrite <- IHh. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 5 stars, optional (palindrome_converse) *)
(** Using your definition of [pal] from the previous exercise, prove
    that
     forall l, l = rev l -> pal l.
*)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 4 stars, advanced (subsequence) *)
(** A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,
    [1,2,3]
    is a subsequence of each of the lists
    [1,2,3]
    [1,1,1,2,2,3]
    [1,2,7,3]
    [5,6,1,9,9,2,7,3,8]
    but it is _not_ a subsequence of any of the lists
    [1,2]
    [1,3]
    [5,6,2,1,7,3,8]

    - Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence. (Hint: You'll need
      three cases.)

    - Prove that subsequence is reflexive, that is, any list is a
      subsequence of itself.  

    - Prove that for any lists [l1], [l2], and [l3], if [l1] is a
      subsequence of [l2], then [l1] is also a subsequence of [l2 ++
      l3].

    - (Optional, harder) Prove that subsequence is transitive -- that
      is, if [l1] is a subsequence of [l2] and [l2] is a subsequence
      of [l3], then [l1] is a subsequence of [l3].  Hint: choose your
      induction carefully!
*)

(* FILL IN HERE *)
(** [] *)


(** **** Exercise: 2 stars, optional (R_provability) *)
(** Suppose we give Coq the following definition:
    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.
    Which of the following propositions are provable?

    - [R 2 [1,0]]
    - [R 1 [1,2,1,0]]
    - [R 6 [3,2,1,0]]
*)

(** [] *)


(* ##################################################### *)
(* ##################################################### *)
(* ##################################################### *)
(* ##################################################### *)

(* $Date: 2013-01-30 19:12:43 -0500 (Wed, 30 Jan 2013) $ *)



