-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_nonnegative_kernel_reflected_integral_le_global
-- name    : AvramDividend.Classical.causal_nonnegative_kernel_reflected_integral_le_global
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T21:43:53.314505+00:00
-- url     : https://prove2.me/theorems/a60caa67-baf0-4190-8f68-a538d520c5bd
-- title:
--   Finite causal reflected mass is bounded by the total nonnegative kernel mass
-- statement:
--   For a nonnegative integrable kernel on positive lags, its reflected integral over a finite causal interval is at most its total integral over positive time. Use the proved positive-Ioc causal convolution commutativity with constant 1 to reverse the interval, then apply the pinned Mathlib setIntegral_mono_set to extend from (0,x] to (0,∞). This supplies the truncation estimate in the weighted Volterra contraction and uniqueness argument.
-- source:
--   Proved positive_Ioc_causal_convolution_comm_real; pinned Mathlib MeasureTheory.setIntegral_mono_set.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_positive_Ioc_causal_convolution_comm_real
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_nonnegative_kernel_reflected_integral_le_global
    (K : ℝ → ℝ) (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hKnonneg : ∀ t : ℝ, 0 < t → 0 ≤ K t)
    (x : ℝ) (hx : 0 < x) :
    (∫ s in Ioc (0 : ℝ) x, K (x - s) ∂volume) ≤
      ∫ s in Ioi (0 : ℝ), K s ∂volume := by sorry
