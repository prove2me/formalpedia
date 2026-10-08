-- Prove2me | Theorems.Thm_FastBestSubset_CDSS_lemma_5
-- name    : FastBestSubset.CDSS.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:27.929574+00:00
-- url     : https://prove2.me/theorems/00d4e2a2-1815-4d2a-b468-6f0eae2b2593
-- title:
--   Lemma 5 — Algorithm 1 is a descent algorithm and F(βᵏ) ↓ F* for some F* ≥ 0
-- statement:
--   Let $X\in\mathbb R^{n\times p}$ have columns of unit Euclidean norm, let $y\in\mathbb R^n$, $\lambda_0>0$, $\lambda_1,\lambda_2\ge0$, let $C$ be a positive integer, and let $\{\beta^k\}$ be the iterates of Algorithm 1 (cyclic coordinate descent with spacer steps) for Problem (2), started at any $\beta^0\in\mathbb R^p$. Then
--   $$F(\beta^{k+1})\le F(\beta^k)\quad\text{for every }k,\qquad\text{and}\qquad F(\beta^k)\to F^*\ \text{ for some } F^*\ge0 .$$
--
--   Monotone descent is the first ingredient of the convergence analysis: the limit $F^*$ is shared by all limit points of the iterates.
--
--   **Formalization Note** The iterates are those of the deterministic CDSS state machine of the Setting file; $k$ counts spacer and non-spacer steps alike.
-- source:
--   Hazimeh, Mazumder, Fast Best Subset Selection: Coordinate Descent and Local Combinatorial Optimization Algorithms, arXiv:1803.01454v3, Lemma 5, p. 12 (proof §A.4, p. 37)

import Mathlib
import Definitions.Def_FastBestSubset_CDSS_Setting

open Filter Topology

namespace FastBestSubset.CDSS

/-- Lemma 5 (p. 12): Algorithm 1 is a descent algorithm and `F(βᵏ) ↓ F*` for some `F* ≥ 0`. -/
theorem lemma_5 {n p : ℕ} [NeZero p] (D : Data n p) (hX : ∀ j, ∑ r, D.X r j ^ 2 = 1)
    (hlam0 : 0 < D.lam0) (hlam1 : 0 ≤ D.lam1) (hlam2 : 0 ≤ D.lam2)
    (C : ℕ) (hC : 0 < C) (β0 : Fin p → ℝ) :
    (∀ k, F D (iter D C β0 (k + 1)) ≤ F D (iter D C β0 k)) ∧
      ∃ Fstar : ℝ, 0 ≤ Fstar ∧ Tendsto (fun k => F D (iter D C β0 k)) atTop (𝓝 Fstar) := by sorry

end FastBestSubset.CDSS
