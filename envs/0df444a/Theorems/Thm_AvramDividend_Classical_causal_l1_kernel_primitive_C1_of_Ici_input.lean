-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_primitive_C1_of_Ici_input
-- name    : AvramDividend.Classical.causal_l1_kernel_primitive_C1_of_Ici_input
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:17:24.673992+00:00
-- url     : https://prove2.me/theorems/91b2c27b-a439-4735-bcf3-94735a6b45e6
-- title:
--   C1 causal convolution from globally integrable derivative kernel and continuous nonnegative-time input
-- statement:
--   If k is L1 on the positive half-line and g(x)=∫_0^x k for x>0, then the causal convolution f*g is C1 on positive times for every input f continuous on [0,∞), without requiring global input integrability. This combines the Proved finite-horizon Fubini smoothing theorem with the Proved L1 causal-convolution continuity and finite-window outer integrability lemmas. It is an independent, source-complete link for localising the canonical monotone-kernel regularity theorem.
-- source:
--   Proved causal_local_fubini_C1_of_convolution_regular d88dacb5-8ede-402e-9552-62110ce7ea68; causal_l1_convolution_continuousOn_positive_of_Ici_input 3bc68f22-45b2-4d9a-b616-0898a3747c78; causal_l1_convolution_outer_integrable 06415ce0-246b-403e-80e6-2d5640185f62; causal_convolution_time_reversal f1622c94-540f-40cd-980d-3b1132ca67c4.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_local_fubini_C1_of_convolution_regular
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_continuousOn_positive_of_Ici_input
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_outer_integrable
import Theorems.Thm_AvramDividend_Classical_causal_convolution_time_reversal
open AvramDividend.Classical MeasureTheory Set intervalIntegral

theorem AvramDividend.Classical.causal_l1_kernel_primitive_C1_of_Ici_input
    (f k g : ℝ → ℝ)
    (hf : ContinuousOn f (Ici (0 : ℝ)))
    (hk : IntegrableOn k (Ioi (0 : ℝ)) volume)
    (hg : ∀ x : ℝ, 0 < x →
      (∫ s in Ioc (0 : ℝ) x, k s ∂volume) = g x) :
    ContDiffOn ℝ 1
      (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
        f s * g (x - s) ∂volume) (Ioi (0 : ℝ)) := by sorry
