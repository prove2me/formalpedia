-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_continuousOn_positive_of_Ici_input
-- name    : AvramDividend.Classical.causal_l1_convolution_continuousOn_positive_of_Ici_input
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T06:54:52.1781+00:00
-- url     : https://prove2.me/theorems/3bc68f22-45b2-4d9a-b616-0898a3747c78
-- title:
--   Positive-time continuity of L1 causal convolution for any nonnegative-time continuous input
-- statement:
--   If K is integrable for positive times and V is continuous on [0,∞), the causal integral x↦∫_(0,x]K(x−s)V(s)ds is continuous on (0,∞). Decompose V(s) into V(0) and V(s)−V(0). The constant part is the reflected kernel mass, while the deviation has a globally continuous zero extension. Apply previously proved convolution regularity and the convolution-splitting identity.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_causal_zero_extension_continuous_of_Ici_zero
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_continuousOn_positive_of_zero_extension
import Theorems.Thm_AvramDividend_Classical_causal_reflected_kernel_mass_continuousOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_causal_convolution_split_at_input_origin
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_l1_convolution_continuousOn_positive_of_Ici_input
    (K V : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hV : ContinuousOn V (Ici (0 : ℝ))) :
    ContinuousOn (fun x : ℝ =>
      ∫ s in Ioc (0 : ℝ) x, K (x - s) * V s ∂volume)
      (Ioi (0 : ℝ)) := by sorry
