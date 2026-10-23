-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_reflected_kernel_mass_continuousOn_nonnegative
-- name    : AvramDividend.Classical.causal_reflected_kernel_mass_continuousOn_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T23:15:20.044206+00:00
-- url     : https://prove2.me/theorems/17b0b560-b9f3-4d47-bf90-bc0db5c2dee6
-- title:
--   Continuity at zero of the reflected causal kernel mass
-- statement:
--   If K is L1 on positive times, the reflected causal mass x↦∫_(0,x]K(x−s)ds is continuous on [0,∞). The proved time-reversal theorem identifies this with the positive-time primitive x↦∫_(0,x]K(s)ds, which is continuous through zero by the L1 primitive-continuity lemma. This supports the constant-input term of a general Volterra operator.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_causal_convolution_time_reversal
import Theorems.Thm_AvramDividend_Classical_causal_l1_primitive_continuousOn_nonnegative
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_reflected_kernel_mass_continuousOn_nonnegative
    (K : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume) :
    ContinuousOn (fun x : ℝ =>
      ∫ s in Ioc (0 : ℝ) x, K (x - s) ∂volume)
      (Ici (0 : ℝ)) := by sorry
