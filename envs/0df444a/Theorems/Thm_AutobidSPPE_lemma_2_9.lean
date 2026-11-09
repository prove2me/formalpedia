-- Prove2me | Theorems.Thm_AutobidSPPE_lemma_2_9
-- name    : AutobidSPPE.lemma_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:59:29.481606+00:00
-- url     : https://prove2.me/theorems/00440a97-21c5-46ab-ab0d-25edda3fe0f4
-- title:
--   Lemma 2.9 — uniform spending has a P-Jacobian
-- statement:
--   Let $n\ge2$. The endpoint spending map $\mathsf s=(\mathsf s_1,\dots,\mathsf s_n)$ is continuously differentiable on $(0,\infty)^n$, and at every $y\in(0,\infty)^n$ both
--   $$
--   J_s=D_y\mathsf s\qquad\text{and}\qquad J_s\,\mathrm{diag}(y_i)
--   $$
--   are P-matrices (all nonempty principal minors positive).
--
--   This is the structural property that drives uniqueness and the regularity of conditional equilibria.
--
--   Differences from the source: none.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Lemma 2.9, p.15

import Mathlib
import Definitions.Def_AutobidSPPE_endpointSpend
import Definitions.Def_AutobidSPPE_spendJac
import Definitions.Def_PriceRobust_Stability_ZPMatrix

namespace AutobidSPPE

/-- Lemma 2.9, p.15 (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6)): the endpoint spending map `𝗌` is continuously differentiable on
`(0, ∞)ⁿ`, and at every point of `(0, ∞)ⁿ` its endpoint Jacobian `J_s = D_y𝗌` and its
log-endpoint Jacobian `J_s diag(yᵢ)` are P-matrices. -/
theorem lemma_2_9 {n : ℕ} (hn : 2 ≤ n) :
    ContDiffOn ℝ 1 (fun y : Fin n → ℝ => fun i => endpointSpend y i) {y | ∀ i, 0 < y i} ∧
    ∀ y : Fin n → ℝ, (∀ i, 0 < y i) →
      PriceRobust.Stability.IsPMatrix (spendJac y) ∧
      PriceRobust.Stability.IsPMatrix (spendJac y * Matrix.diagonal y) := by sorry

end AutobidSPPE
