-- Prove2me | Theorems.Thm_EnvyFreeCake104_Divide_claim_7
-- name    : EnvyFreeCake104.Divide.claim_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:09:56.515942+00:00
-- url     : https://prove2.me/theorems/28b14736-b9c5-4b5f-8ea1-07aaaeb21183
-- title:
--   Claim 7: every envy-free suffix allocation lies inside its candidate
-- statement:
--   Let $N$ be a set of agents and $(P_i)_{i\in N}$ pairwise disjoint pieces. Fix an agent order $i_1,\dots,i_n$ and a piece order $j_1,\dots,j_n$ (each an enumeration of $N$ without repetition), and let $Y$ be the candidate that Permute builds for these orders (from any record state valid for $N$ in which the pieces are aligned). If $Z$ is an envy-free allocation among $N$ in which every $Z_{i_r}$ is a suffix of $P_{j_r}$, then
--   $$Z_{i_r}\subseteq Y_{i_r}\qquad\text{for all } r=1,\dots,n .$$
--   The statement also asserts that building the candidate succeeds.
--
--   This is the containment step in the proof that some guess of Permute succeeds: an envy-free suffix allocation with the guessed assignment is squeezed inside the candidate.
--
--   Differences from the source:
--   - encoding: a set N of n agents, relabeled 1, …, n inside each call (§1.3) → a Finset N of an agent type ι with decidable equality; bijections onto {1,…,n} become maps ι → ι bijective on N; reason: relabeling is notation; every instance of the source is an instance of the Lean statement and conversely
--   - encoding: Robertson–Webb queries with recorded values (p.1, §1.3) → protocols are programs over an oracle with exactly the operations Eval_i([a,b)) and Cut_i(x,w), keeping the recorded-value table in their own state; the query count is the number of Eval and Cut events in the run's transcript; reason: the program sees the valuations only through query answers, so the count is the source's query count; a prefix cut issues one Cut query and one Eval per participating agent only when it creates a new point, as in §1.3
--   - encoding: every piece handled is a union of recorded cells, and calls inherit the records (§1.3) → hypotheses Rec.Valid V N s (records correct for the participating agents) and Rec.Aligned (every endpoint recorded) on an arbitrary initial record state; reason: this is the source's standing convention for every protocol call; the statement holds for every record state satisfying it
--   - encoding: a piece is a finite union of disjoint intervals of [0,1] with a specified interval order; intervals are [a,b), except the one ending at 1, which contains 1 (§1.3) → Piece = List Interval with Piece.WF (endpoints in [0,1], pairwise disjoint intervals); Interval.toSet is Icc a 1 when b = 1 and a < b, else Ico a b; reason: the source's convention, implemented literally
--   - reading: intervals ending at 1 include that endpoint (§1.3); the degenerate case [1,1) is not discussed → a degenerate interval [a,a) is empty, also for a = 1; reason: cutting [a,1] at x = 1 must give [a,1] and the empty piece for the prefix/suffix split to partition the interval; reading [1,1] as {1} would make the empty suffix of a piece ending at 1 non-empty
--   - encoding: nonnegative integrable density v_i on [0,1], V_i(P) = ∫_P v_i (p.1) → Valuation: density nonnegative on [0,1] and IntegrableOn [0,1]; value S = ∫ over S ∩ [0,1]; reason: same objects; recursive calls take unnormalized, possibly zero valuations, as on p.5
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.14, Claim 7

import Definitions.Def_EnvyFreeCake104_Divide_Protocols

set_option autoImplicit false

namespace EnvyFreeCake104.Divide

/-- Claim 7 (p.14). Fix an agent order `ag = [i_1, …, i_n]` and a piece order
`pc = [j_1, …, j_n]` of `N`, and let `Y` be the corresponding candidate built by Permute.
If `Z` is an envy-free allocation in which every `Z_{i_r}` is a suffix of `P_{j_r}`, then
`Z_{i_r} ⊆ Y_{i_r}` for every `r`. -/
theorem claim_7 {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (P : ι → Piece) (hP : ∀ i ∈ N, (P i).WF)
    (hPdisj : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → Disjoint (P i).toSet (P j).toSet)
    (s : Rec ι) (hs : s.Valid V N) (hPs : ∀ i ∈ N, s.Aligned (P i))
    (ag pc : List ι) (hag : ag.Nodup ∧ ag.toFinset = N) (hpc : pc.Nodup ∧ pc.toFinset = N)
    (o : ChoiceOracle ι) :
    ∃ (Y : ι → Piece) (R : Piece) (s' : Rec ι) (tr : List (Event ι)),
      exec V o (candidate N P ag pc) s = some ((Y, R), s', tr) ∧
      ∀ Z : ι → Set ℝ, EnvyFree V N Z →
        (∀ p ∈ ag.zip pc, IsSuffix (Z p.1) (P p.2)) →
        ∀ p ∈ ag.zip pc, Z p.1 ⊆ (Y p.1).toSet := by sorry

end EnvyFreeCake104.Divide
