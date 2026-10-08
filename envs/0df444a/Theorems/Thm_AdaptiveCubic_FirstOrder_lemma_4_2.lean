-- Prove2me | Theorems.Thm_AdaptiveCubic_FirstOrder_lemma_4_2
-- name    : AdaptiveCubic.FirstOrder.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:38:14.031208+00:00
-- url     : https://prove2.me/theorems/d6328fce-2dca-49d3-812f-b60f73453ee3
-- title:
--   Lemma 4.2 — (4.1) and (4.2) give the model decrease σ_k‖s_k‖³/6
-- statement:
--   Let $m_k$ be the cubic model (1.2) at $x_k$ with symmetric approximation $B_k$ and weight $\sigma_k$. If the step $s_k$ satisfies
--
--   1. (4.1) $\;g_k^\top s_k+s_k^\top B_k s_k+\sigma_k\|s_k\|^3=0$, and
--   2. (4.2) $\;s_k^\top B_k s_k+\sigma_k\|s_k\|^3\ge0$,
--
--   then
--
--   $$f(x_k)-m_k(s_k)\ge\frac16\,\sigma_k\|s_k\|^3.$$
--
--   The decrease predicted by the model is thus controlled from below by the length of the step alone. Combined with a lower bound on $\|s_k\|$ (Lemma 5.2), this gives the model decrease used for the $\epsilon^{-3/2}$ complexity bound.
--
--   **Formalization Note** The statement is about a single iteration: $f$, $x_k$, $B_k$, $\sigma_k$ and $s_k$ are arbitrary, no run is involved. No sign condition on $\sigma_k$ or symmetry of $B_k$ is needed.
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 11, Lemma 4.2, (4.4) (= Part I, Lemma 3.3)

import Mathlib
import Definitions.Def_AdaptiveCubic_Cauchy_model

open scoped RealInnerProductSpace

namespace AdaptiveCubic.FirstOrder

/-- Lemma 4.2, p. 11 (Cartis, Gould & Toint, ARC Part II, preprint rev. 15 Sep 2009; = Part I,
Lemma 3.3). If `s_k` satisfies (4.1), `g_kᵀ s_k + s_kᵀ B_k s_k + σ_k‖s_k‖³ = 0`, and (4.2),
`s_kᵀ B_k s_k + σ_k‖s_k‖³ ≥ 0`, then `f(x_k) − m_k(s_k) ≥ (1/6) σ_k ‖s_k‖³` (4.4). -/
theorem lemma_4_2 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (σ : ℝ) (x sk : EuclideanSpace ℝ (Fin n))
    (h41 : ⟪gradient f x, sk⟫ + ⟪sk, B sk⟫ + σ * ‖sk‖ ^ 3 = 0)
    (h42 : 0 ≤ ⟪sk, B sk⟫ + σ * ‖sk‖ ^ 3) :
    1 / 6 * σ * ‖sk‖ ^ 3 ≤ f x - AdaptiveCubic.Cauchy.model f B σ x sk := by sorry

end AdaptiveCubic.FirstOrder
