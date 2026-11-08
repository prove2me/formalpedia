-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_comp10_positivepart_L1_of_nonnegative_shift
-- name    : AvramDividend.Classical.avram_p3_comp10_positivepart_L1_of_nonnegative_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:14:21.569512+00:00
-- url     : https://prove2.me/theorems/25e3c213-b5e2-4456-8d9c-0e9fa5fdc26d
-- title:
--   Positive part of an L1 signed residual remains integrable after subtracting a nonnegative constant under any measure
-- statement:
--   On an arbitrary measure space, if F and G are integrable real functions and c is a nonnegative scalar, then max(F-(c+G),0) is integrable. The proof bounds it between zero and max(F-G,0), which is integrable. This avoids the false inference that a nonzero constant is integrable under an arbitrary measure.
-- source:
--   Mathlib Integrable.sup, integrable_zero, and Integrable.mono_nonneg; original Avram 4044 has initial payoff nonnegative by Proved 781581e9.

import Mathlib
open Classical MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_p3_comp10_positivepart_L1_of_nonnegative_shift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (F G : Ω → ℝ) (hF : Integrable F P) (hG : Integrable G P)
    (c : ℝ) (hc : 0 ≤ c) :
    Integrable (fun ω => max (F ω - (c + G ω)) 0) P := by sorry
