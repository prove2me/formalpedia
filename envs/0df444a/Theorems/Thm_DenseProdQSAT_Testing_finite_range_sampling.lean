-- Prove2me | Theorems.Thm_DenseProdQSAT_Testing_finite_range_sampling
-- name    : DenseProdQSAT.Testing.finite_range_sampling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:43.892895+00:00
-- url     : https://prove2.me/theorems/dbe0dc65-9857-4ce5-9bd6-8afa268c686b
-- title:
--   Lemma 4.2 — uniform subset sampling in a finite range space
-- statement:
--   Let $U$ be any nonempty finite universe and $\mathcal R\subseteq2^U$ any range family. Let $\pi_{\mathcal R}$ be its actual growth function on tuples. Suppose $0<\alpha<1$, $1\le m\le|U|$, and $\alpha m\ge8$. If $S$ is uniform on the unordered $m$-element subsets of $U$, then
--
--   $$\Pr[\exists R\in\mathcal R:\ |R|\ge\alpha|U|\ \text{and}\ S\cap R=\varnothing]\le2\pi_{\mathcal R}(2m)\exp(-\alpha m/4).$$
--
--   This is sampling without replacement, with a non-strict density threshold and the growth function evaluated at $2m$ even when $2m>|U|$. It is the sampling tool used after restricting away a fixed support.
--
--   Differences from the source: none.
-- source:
--   Xuhong Liu, Shuai Shao, Zicheng Han, Xiande Zhang, STOC 2027 submission #35 (October 2026), Lemma 4.2, p. 12

import Definitions.Def_DenseProdQSAT_Testing_FiniteRanges
set_option autoImplicit false

namespace DenseProdQSAT.Testing

theorem finite_range_sampling {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]
    (ℛ : Set (Finset U)) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (m : ℕ) (hm : 1 ≤ m) (hmU : m ≤ Fintype.card U) (hαm : 8 ≤ α * m) :
    SubsetProbability Finset.univ m (fun S => ∃ R ∈ ℛ,
      α * Fintype.card U ≤ (R.card : ℝ) ∧ Disjoint S R) ≤
        2 * Growth ℛ (2 * m) * Real.exp (-α * m / 4) := by sorry

end DenseProdQSAT.Testing
