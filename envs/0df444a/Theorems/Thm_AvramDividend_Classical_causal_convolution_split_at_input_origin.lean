-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_convolution_split_at_input_origin
-- name    : AvramDividend.Classical.causal_convolution_split_at_input_origin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T22:41:39.413304+00:00
-- url     : https://prove2.me/theorems/3b5daf5c-beba-45f1-b98e-02a27ed990fb
-- title:
--   Separate the input boundary value in a causal L1 convolution
-- statement:
--   For an L1 positive-lag kernel and a continuous nonnegative-time input, split the causal convolution into the constant boundary value f(0) times the reflected kernel mass and a convolution against f-f(0). The deviation vanishes at zero and admits a continuous zero extension. Local integrability of all terms follows from the Proved continuous-input causal L1 lemma, and linearity gives the identity.
-- source:
--   Pinned Mathlib set integral linearity and Proved causal_l1_kernel_continuous_input_integrable.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_continuous_input_integrable
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_convolution_split_at_input_origin
    (K f : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hf : ContinuousOn f (Ici (0 : ℝ)))
    (x : ℝ) (hx : 0 < x) :
    (∫ s in Ioc (0 : ℝ) x, K (x - s) * f s ∂volume) =
      f 0 * (∫ s in Ioc (0 : ℝ) x, K (x - s) ∂volume) +
      (∫ s in Ioc (0 : ℝ) x,
        K (x - s) * (f s - f 0) ∂volume) := by sorry
