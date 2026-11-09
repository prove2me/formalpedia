-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_lemma_3
-- name    : EnvyFreeCake104.Divide.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:10:39.561191+00:00
-- url     : https://prove2.me/theorems/285187a7-b6ea-4e38-bca1-5cfc5b97af68
-- title:
--   Lemma 3: Core gives the cutter exactly $V_c(C)/n$ with at most $n^3(n!)^2$ queries
-- statement:
--   Let $N$ be a set of $n\ge 2$ agents, $C$ a cake (a well-formed piece, possibly empty, possibly of value zero to some agents) and $c\in N$ a designated cutter. For every valid record state in which $C$ is aligned and every choice oracle, Core$(c,N,C)$ terminates and returns a partial envy-free allocation $Y$ of $C$ with residue $U=C\setminus\bigcup_{i\in N}Y_i$, in which
--   $$V_c(Y_c)=\frac{V_c(C)}{n},$$
--   and the run makes at most $n^3(n!)^2$ Robertson–Webb queries.
--
--   Core is the subroutine that gives a chosen agent exactly a $1/n$ share of the remaining cake; Dominate calls it repeatedly to shrink the residue.
--
--   Differences from the source:
--   - encoding: a set N of n agents, relabeled 1, …, n inside each call (§1.3) → a Finset N of an agent type ι with decidable equality; bijections onto {1,…,n} become maps ι → ι bijective on N; reason: relabeling is notation; every instance of the source is an instance of the Lean statement and conversely
--   - encoding: the protocol's free choices (cutter c, Line 7 tuple, dominated group, round-robin order and tie-breaks, Cut-and-Choose roles and tie-break, Permute's enumeration order) are made arbitrarily → every free choice is resolved by an arbitrary choice oracle (a function of the transcript so far), quantified universally; a step with no admissible option fails; reason: the source's protocol is correct for every resolution of its choices; a universal quantifier over adaptive oracles covers each resolution
--   - encoding: Robertson–Webb queries with recorded values (p.1, §1.3) → protocols are programs over an oracle with exactly the operations Eval_i([a,b)) and Cut_i(x,w), keeping the recorded-value table in their own state; the query count is the number of Eval and Cut events in the run's transcript; reason: the program sees the valuations only through query answers, so the count is the source's query count; a prefix cut issues one Cut query and one Eval per participating agent only when it creates a new point, as in §1.3
--   - encoding: every piece handled is a union of recorded cells, and calls inherit the records (§1.3) → hypotheses Rec.Valid V N s (records correct for the participating agents) and Rec.Aligned (every endpoint recorded) on an arbitrary initial record state; reason: this is the source's standing convention for every protocol call; the statement holds for every record state satisfying it
--   - encoding: a piece is a finite union of disjoint intervals of [0,1] with a specified interval order; intervals are [a,b), except the one ending at 1, which contains 1 (§1.3) → Piece = List Interval with Piece.WF (endpoints in [0,1], pairwise disjoint intervals); Interval.toSet is Icc a 1 when b = 1 and a < b, else Ico a b; reason: the source's convention, implemented literally
--   - reading: intervals ending at 1 include that endpoint (§1.3); the degenerate case [1,1) is not discussed → a degenerate interval [a,a) is empty, also for a = 1; reason: cutting [a,1] at x = 1 must give [a,1] and the empty piece for the prefix/suffix split to partition the interval; reading [1,1] as {1} would make the empty suffix of a piece ending at 1 non-empty
--   - encoding: nonnegative integrable density v_i on [0,1], V_i(P) = ∫_P v_i (p.1) → Valuation: density nonnegative on [0,1] and IntegrableOn [0,1]; value S = ∫ over S ∩ [0,1]; reason: same objects; recursive calls take unnormalized, possibly zero valuations, as on p.5
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.6, Lemma 3 (restated p.10)

import Definitions.Def_EnvyFreeCake104_Divide_Protocols

set_option autoImplicit false

namespace EnvyFreeCake104.Divide

/-- Lemma 3 (p.6, restated p.10). For `n ≥ 2` agents, a cake `C` (possibly empty, possibly
worth zero to some agents) and a cutter `c ∈ N`, Core returns a partial envy-free allocation
`Y` of `C` with residue `U` and `V_c(Y_c) = V_c(C)/n`, using at most `n³(n!)²` queries. -/
theorem lemma_3 {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (hN : 2 ≤ N.card) (c : ι) (hc : c ∈ N) (C : Piece) (hC : C.WF)
    (s : Rec ι) (hs : s.Valid V N) (hCs : s.Aligned C) (o : ChoiceOracle ι) :
    ∃ (Y : ι → Piece) (U : Piece) (s' : Rec ι) (tr : List (Event ι)),
      exec V o (core N c C) s = some ((Y, U), s', tr) ∧
      IsPartialAlloc N C.toSet (fun i => (Y i).toSet) ∧
      U.toSet = residue N C.toSet (fun i => (Y i).toSet) ∧
      EnvyFree V N (fun i => (Y i).toSet) ∧
      (V c).value (Y c).toSet = (V c).value C.toSet / (N.card : ℝ) ∧
      queryCount tr ≤ N.card ^ 3 * (N.card.factorial) ^ 2 := by sorry

end EnvyFreeCake104.Divide
