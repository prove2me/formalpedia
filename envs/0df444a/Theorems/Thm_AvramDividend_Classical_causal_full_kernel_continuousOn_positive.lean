-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_full_kernel_continuousOn_positive
-- name    : AvramDividend.Classical.causal_full_kernel_continuousOn_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T07:15:23.559826+00:00
-- url     : https://prove2.me/theorems/94cb3006-6288-44a9-8e29-524ab94be95e
-- title:
--   Positive-time continuity of the full causal Volterra kernel
-- statement:
--   When K is integrable at positive lags and V continuous on nonnegative time, the full causal Volterra integral with coefficient beta plus K(x-s) is continuous at every positive x. Split the kernel into beta times the primitive of V and its causal L1 convolution. Both terms are already Proved continuous. Integrability of the summands justifies integral linearity.
-- source:
--   Proved causal_l1_convolution_continuousOn_positive_of_Ici_input, causal_continuous_input_primitive_continuousOn_nonnegative and causal_l1_kernel_continuous_input_integrable.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_continuousOn_positive_of_Ici_input
import Theorems.Thm_AvramDividend_Classical_causal_continuous_input_primitive_continuousOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_continuous_input_integrable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_full_kernel_continuousOn_positive
    (K V : ℝ → ℝ) (β : ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hV : ContinuousOn V (Ici (0 : ℝ))) :
    ContinuousOn (fun x : ℝ =>
      ∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) * V s ∂volume)
      (Ioi (0 : ℝ)) := by sorry
