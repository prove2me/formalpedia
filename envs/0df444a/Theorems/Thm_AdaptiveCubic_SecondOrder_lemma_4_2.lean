-- Prove2me | Theorems.Thm_AdaptiveCubic_SecondOrder_lemma_4_2
-- name    : AdaptiveCubic.SecondOrder.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:38:19.340004+00:00
-- url     : https://prove2.me/theorems/6e35b690-4a26-443a-9ee9-bb76f4a06c6f
-- title:
--   Lemma 4.2 — (4.1) and (4.2) give the model decrease σ_k‖s_k‖³/6
-- statement:
--   Suppose the step $s_k$ satisfies (4.1), $g_k^\top s_k+s_k^\top B_ks_k+\sigma_k\|s_k\|^3=0$, and (4.2), $s_k^\top B_ks_k+\sigma_k\|s_k\|^3\ge0$. Then
--
--   $$f(x_k)-m_k(s_k)\ \ge\ \tfrac16\,\sigma_k\|s_k\|^3. \qquad (4.4)$$
--
--   This is the decrease of the model that every ARC(S) step achieves, and it is the link between the step length and the decrease of $f$ in all complexity bounds for ARC(S).
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 11, Lemma 4.2

import Mathlib
import Definitions.Def_AdaptiveCubic_Cauchy_model

open scoped RealInnerProductSpace

namespace AdaptiveCubic.SecondOrder

/-- Lemma 4.2, p. 11 (Cartis, Gould & Toint, ARC Part II, preprint rev. 15 Sep 2009; = Part I,
Lemma 3.3). If `s_k` satisfies (4.1), `g_kᵀ s_k + s_kᵀ B_k s_k + σ_k‖s_k‖³ = 0`, and (4.2),
`s_kᵀ B_k s_k + σ_k‖s_k‖³ ≥ 0`, then `f(x_k) − m_k(s_k) ≥ (1/6) σ_k ‖s_k‖³` (4.4). -/
theorem lemma_4_2 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (σ : ℝ) (x sk : EuclideanSpace ℝ (Fin n))
    (h41 : ⟪gradient f x, sk⟫ + ⟪sk, B sk⟫ + σ * ‖sk‖ ^ 3 = 0)
    (h42 : 0 ≤ ⟪sk, B sk⟫ + σ * ‖sk‖ ^ 3) :
    1 / 6 * σ * ‖sk‖ ^ 3 ≤ f x - AdaptiveCubic.Cauchy.model f B σ x sk := by sorry

end AdaptiveCubic.SecondOrder
