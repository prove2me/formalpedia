-- Prove2me | Theorems.Thm_AdaptiveCubic_Cauchy_lemma_3_1_ii
-- name    : AdaptiveCubic.Cauchy.lemma_3_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:43:49.782365+00:00
-- url     : https://prove2.me/theorems/98b417b9-6994-4ee2-a5a0-a01807a483bd
-- title:
--   Lemma 3.1 ii) (3.4) — $\|s\|\le(3/\sigma)\max(\kappa_B,\sqrt{\sigma\|g\|})$
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$, $x\in\mathbb R^n$ with gradient $g=\nabla f(x)$, $B$ a symmetric matrix with $\|B\|\le\kappa_B$ for some $\kappa_B\ge0$ (assumption AM.1), and $\sigma>0$. If the step $s$ satisfies the Cauchy condition (2.2), then
--
--   $$
--   \|s\|\le\frac{3}{\sigma}\max\left(\kappa_B,\ \sqrt{\sigma\|g\|}\right).
--   $$
--
--   The bound says that the cubic term keeps the step of order $\sqrt{\|g\|/\sigma}$ once $\sigma\|g\|$ dominates the curvature bound. It is quoted from Part I of the paper (Lemma 2.2 there) and is used to bound the Taylor remainder in Lemma 3.2.
--
--   **Formalization Note** One iteration, index $k$ dropped; $\|B\|$ is the operator norm.
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 7, Lemma 3.1 ii), (3.4)

import Mathlib
import Definitions.Def_AdaptiveCubic_Cauchy_IsARCRun

open scoped RealInnerProductSpace

namespace AdaptiveCubic.Cauchy

/-- Lemma 3.1 ii), (3.4), p. 7 (Cartis, Gould & Toint, ARC Part II, preprint rev. 15 Sep 2009;
quoted from Part I, Lemma 2.2). For one iteration with iterate `x`, symmetric `B` with
`‖B‖ ≤ κ_B` (AM.1, `κ_B ≥ 0`), weight `σ > 0` and a step `s` satisfying the Cauchy condition (2.2):
`‖s‖ ≤ (3/σ) max(κ_B, √(σ ‖g‖))`, with `g = ∇f(x)`. -/
theorem lemma_3_1_ii {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hB : IsSelfAdjoint B)
    (κB : ℝ) (hκB : 0 ≤ κB) (hAM1 : ‖B‖ ≤ κB)
    (σ : ℝ) (hσ : 0 < σ) (x s : EuclideanSpace ℝ (Fin n))
    (hcauchy : ∀ α : ℝ, 0 ≤ α → model f B σ x s ≤ model f B σ x (-(α • gradient f x))) :
    ‖s‖ ≤ 3 / σ * max κB (√(σ * ‖gradient f x‖)) := by sorry

end AdaptiveCubic.Cauchy
