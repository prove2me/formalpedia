-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_withDensity_independent_atomless_clock_no_stopping_tie
-- name    : AvramDividend.Classical.avram_ws01e_b_withDensity_independent_atomless_clock_no_stopping_tie
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T12:46:44.9871+00:00
-- url     : https://prove2.me/theorems/2876fc1d-aa70-4e7e-8ffc-f82857d21408
-- title:
--   Independent atomless observation clock remains unequal to measurable stopping age under any density tilt
-- statement:
--   For independent path and atomless clock probability measures P and Q, any measurable nonnegative stopping age τ on paths and any measurable clock e, the tie event τ=e is zero not only under P×Q but also under every absolutely continuous density tilt (P×Q).withDensity w, without requiring a globally tilted process or normalisation of the density. This closes the strict-versus-weak clock-order gap needed to condition a genuine random-terminal Esscher law at a capped first record.
-- source:
--   Proved avram_ws01e_b_independent_atomless_clock_no_stopping_age_tie (455a7bf6) and pinned Mathlib withDensity_absolutelyContinuous.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_independent_atomless_clock_no_stopping_age_tie

open AvramDividend.Classical MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_withDensity_independent_atomless_clock_no_stopping_tie
    {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure Θ) [IsProbabilityMeasure Q]
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (e : Θ → ℝ≥0) (he : Measurable e)
    (hAtomless : ∀ a : ℝ≥0, Q {η : Θ | e η = a} = 0)
    (w : Ω × Θ → ℝ≥0∞) :
    ((P.prod Q).withDensity w)
      {z : Ω × Θ | τ z.1 = e z.2} = 0 := by sorry
