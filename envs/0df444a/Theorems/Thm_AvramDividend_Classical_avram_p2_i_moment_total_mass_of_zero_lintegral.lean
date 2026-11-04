-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_total_mass_of_zero_lintegral
-- name    : AvramDividend.Classical.avram_p2_i_moment_total_mass_of_zero_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:31:24.789044+00:00
-- url     : https://prove2.me/theorems/d66f08c1-ec62-45a5-8b46-5f96d3e12d79
-- title:
--   Finite zero-th ENNReal monomial moment gives finite total mass
-- statement:
--   The kth moment k=0 is exactly the total mass of a positive measure. Therefore its finite ENNReal lintegral hypothesis implies the measure is finite; this allows the original-process weighted-image compact-test theorem to infer total-mass finiteness from its all-k moment assumptions instead of assuming it separately.

import Mathlib
open MeasureTheory Filter Topology Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_i_moment_total_mass_of_zero_lintegral
    (μ : Measure ℝ)
    (hfinite : (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ 0 ∂μ) ≠ ⊤) :
    μ Set.univ < ⊤ := by sorry
