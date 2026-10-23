-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_weighted_Ioc_convolution_continuous
-- name    : AvramDividend.Classical.positive_weighted_Ioc_convolution_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T19:07:35.083607+00:00
-- url     : https://prove2.me/theorems/0db1728b-6a0d-46c3-a365-53a59d7d9c1c
-- title:
--   Continuity of a causal convolution with exponentially damped bounded scale factor
-- statement:
--   If e^(−t)f(t) is integrable on t>0 and the positive indicator of e^(−t)g(t) is globally bounded and continuous, then x↦∫_(0,x] f(x−s)g(s) ds is continuous on x>0, without boundedness of g itself. Factor e^(−x) into the integrand, commute the Ioc causal convolution to put the bounded factor on the right, apply the Proved Mathlib positive causal convolution continuity result, and multiply back by the continuous scalar exp x. This is the reusable continuity bridge for the Gaussian Esscher Volterra residual.
-- source:
--   Proved positive_causal_convolution_continuous_bounded_right and positive_Ioc_causal_convolution_comm_real

import Mathlib.Analysis.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_continuous_bounded_right
import Theorems.Thm_AvramDividend_Classical_positive_Ioc_causal_convolution_comm_real
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.positive_weighted_Ioc_convolution_continuous
    (f g : ℝ → ℝ)
    (hf : IntegrableOn (fun t : ℝ => Real.exp (-t) * f t)
      (Ioi (0 : ℝ)) volume)
    (hg : Continuous ((Ioi (0 : ℝ)).indicator
      (fun t : ℝ => Real.exp (-t) * g t)))
    (hgb : BddAbove (Set.range (fun x : ℝ =>
      ‖(Ioi (0 : ℝ)).indicator
         (fun t : ℝ => Real.exp (-t) * g t) x‖))) :
    ContinuousOn (fun x : ℝ =>
      ∫ s in Ioc (0 : ℝ) x, f (x - s) * g s ∂volume)
      (Ioi (0 : ℝ)) := by sorry
