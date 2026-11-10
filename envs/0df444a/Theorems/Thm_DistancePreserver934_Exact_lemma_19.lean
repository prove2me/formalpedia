-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_lemma_19
-- name    : DistancePreserver934.Exact.lemma_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T08:36:17.686486+00:00
-- url     : https://prove2.me/theorems/a243fce7-e2b7-4145-a5bb-16dc5d5fe812
-- title:
--   Lemma 19 (partial set cover)
-- statement:
--   Let $\{A_i:i\in I\}$ be a finite indexed family of finite sets with $M=|I|\ge1$, and put
--   $$\Delta=\sum_{i\in I}|A_i|>0,\qquad\mu(q)=|\{i:q\in A_i\}|.$$
--   If $\mu(q)\le\gamma$ for every element $q$, then there is $J\subseteq I$ such that $Q=\bigcup_{i\in J}A_i$ satisfies
--   $$|Q|\ge\frac{\Delta}{2\gamma},\qquad|J|\le\frac{2M}{\Delta}\,|Q|.\tag{18}$$
--
--   Repeated sets count as separate indices. This purely combinatorial statement selects the covering set $S$ in the proof of Lemma 10.
--
--   Differences from the source: none.
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026), SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b, Lemma 19, printed p. 18 (PDF p. 19)

import Mathlib

namespace DistancePreserver934.Exact

open Classical

/-- Lemma 19 (partial set cover), printed p.18 / PDF p.19.  Let `{A_i : i ∈ I}` be a finite
indexed family of finite sets with `M = |I| ≥ 1`, `Δ = ∑_i |A_i| > 0` and multiplicities
`μ(q) = |{i : q ∈ A_i}| ≤ γ` for every element `q`.  Then there is `J ⊆ I` such that
`Q = ⋃_{i ∈ J} A_i` satisfies `|Q| ≥ Δ/(2γ)` and `|J| ≤ (2M/Δ) |Q|` (Equation (18)). -/
theorem lemma_19 {ι α : Type*} [Fintype ι] [DecidableEq α] (A : ι → Finset α) (γ : ℝ)
    (hM : 1 ≤ Fintype.card ι) (hΔ : 0 < ∑ i, (A i).card)
    (hμ : ∀ q : α, ((Finset.univ.filter (fun i => q ∈ A i)).card : ℝ) ≤ γ) :
    ∃ J : Finset ι,
      ((∑ i, (A i).card : ℕ) : ℝ) / (2 * γ) ≤ ((J.biUnion A).card : ℝ) ∧
      (J.card : ℝ) ≤ 2 * (Fintype.card ι : ℝ) / ((∑ i, (A i).card : ℕ) : ℝ) *
        ((J.biUnion A).card : ℝ) := by sorry

end DistancePreserver934.Exact
