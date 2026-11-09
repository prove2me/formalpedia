-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_lemma_1
-- name    : EnvyFreeCake104.Divide.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:10:14.0642+00:00
-- url     : https://prove2.me/theorems/a57403da-6cad-4563-a769-c8e91378ab62
-- title:
--   Lemma 1: Dominate finds a dominated group with at most $32^n n^7 (n!)^2$ queries
-- statement:
--   Let $N$ be a set of $n\ge3$ agents and $C$ a cake (a well-formed piece; valuations need not be normalized and may be zero on $C$). For every valid record state in which $C$ is aligned and every choice oracle, Dominate$(N,C)$ terminates and returns a partial envy-free allocation $X$ of $C$, its residue $R=C\setminus\bigcup_{i\in N}X_i$, and a set of agents $E$ with $\emptyset\ne E\subsetneq N$ such that every agent $i\notin E$ dominates every agent $j\in E$ in $(X,R)$:
--   $$V_i(X_i)\ge V_i(X_j)+V_i(R).$$
--   The run makes at most $32^n n^7 (n!)^2$ Robertson–Webb queries.
--
--   Lemma 1 reduces envy-free division to the smaller problem of dividing the residue among the dominated group.
--
--   Differences from the source:
--   - encoding: a set N of n agents, relabeled 1, …, n inside each call (§1.3) → a Finset N of an agent type ι with decidable equality; bijections onto {1,…,n} become maps ι → ι bijective on N; reason: relabeling is notation; every instance of the source is an instance of the Lean statement and conversely
--   - encoding: the protocol's free choices (cutter c, Line 7 tuple, dominated group, round-robin order and tie-breaks, Cut-and-Choose roles and tie-break, Permute's enumeration order) are made arbitrarily → every free choice is resolved by an arbitrary choice oracle (a function of the transcript so far), quantified universally; a step with no admissible option fails; reason: the source's protocol is correct for every resolution of its choices; a universal quantifier over adaptive oracles covers each resolution
--   - encoding: Robertson–Webb queries with recorded values (p.1, §1.3) → protocols are programs over an oracle with exactly the operations Eval_i([a,b)) and Cut_i(x,w), keeping the recorded-value table in their own state; the query count is the number of Eval and Cut events in the run's transcript; reason: the program sees the valuations only through query answers, so the count is the source's query count; a prefix cut issues one Cut query and one Eval per participating agent only when it creates a new point, as in §1.3
--   - encoding: every piece handled is a union of recorded cells, and calls inherit the records (§1.3) → hypotheses Rec.Valid V N s (records correct for the participating agents) and Rec.Aligned (every endpoint recorded) on an arbitrary initial record state; reason: this is the source's standing convention for every protocol call; the statement holds for every record state satisfying it
--   - encoding: a piece is a finite union of disjoint intervals of [0,1] with a specified interval order; intervals are [a,b), except the one ending at 1, which contains 1 (§1.3) → Piece = List Interval with Piece.WF (endpoints in [0,1], pairwise disjoint intervals); Interval.toSet is Icc a 1 when b = 1 and a < b, else Ico a b; reason: the source's convention, implemented literally
--   - reading: intervals ending at 1 include that endpoint (§1.3); the degenerate case [1,1) is not discussed → a degenerate interval [a,a) is empty, also for a = 1; reason: cutting [a,1] at x = 1 must give [a,1] and the empty piece for the prefix/suffix split to partition the interval; reading [1,1] as {1} would make the empty suffix of a piece ending at 1 non-empty
--   - encoding: Divide/Dominate terminate (while loops and recursion) → loops and recursion take a fuel argument and fail when it runs out; the statement asserts that some fuel makes the run succeed; reason: fuel is consumed only when another iteration starts, so a successful run is the source's unbounded run; ∃ fuel after ∀ oracle states termination
--   - encoding: nonnegative integrable density v_i on [0,1], V_i(P) = ∫_P v_i (p.1) → Valuation: density nonnegative on [0,1] and IntegrableOn [0,1]; value S = ∫ over S ∩ [0,1]; reason: same objects; recursive calls take unnormalized, possibly zero valuations, as on p.5
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.5, Lemma 1 (restated p.8)

import Definitions.Def_EnvyFreeCake104_Divide_Protocols

set_option autoImplicit false

namespace EnvyFreeCake104.Divide

/-- Lemma 1 (p.5, restated p.8). For `n ≥ 3` agents and a cake `C`, Dominate returns a
partial envy-free allocation `X` of `C`, its residue `R`, and a set `∅ ≠ E ⊊ N` such that
every agent outside `E` dominates every agent of `E` in `(X, R)`, using at most
`32ⁿn⁷(n!)²` queries. -/
theorem lemma_1 {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : 3 ≤ N.card) (C : Piece) (hC : C.WF)
    (s : Rec ι) (hs : s.Valid V N) (hCs : s.Aligned C) (o : ChoiceOracle ι) :
    ∃ (fuel : ℕ) (X : ι → Piece) (R : Piece) (E : Finset ι) (s' : Rec ι) (tr : List (Event ι)),
      exec V o (dominate fuel N C) s = some ((X, R, E), s', tr) ∧
      IsPartialAlloc N C.toSet (fun i => (X i).toSet) ∧
      R.toSet = residue N C.toSet (fun i => (X i).toSet) ∧
      EnvyFree V N (fun i => (X i).toSet) ∧
      IsDominatedGroup V N (fun i => (X i).toSet) R.toSet E ∧
      queryCount tr ≤ 32 ^ N.card * N.card ^ 7 * (N.card.factorial) ^ 2 := by sorry

end EnvyFreeCake104.Divide
