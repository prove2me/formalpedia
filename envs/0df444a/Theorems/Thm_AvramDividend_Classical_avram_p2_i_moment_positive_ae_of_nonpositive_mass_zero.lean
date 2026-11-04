-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_positive_ae_of_nonpositive_mass_zero
-- name    : AvramDividend.Classical.avram_p2_i_moment_positive_ae_of_nonpositive_mass_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:58:42.199142+00:00
-- url     : https://prove2.me/theorems/33ef8692-e478-42d1-ad19-0b79e8a1f4a7
-- title:
--   Zero nonpositive mass gives almost-everywhere strictly positive support
-- statement:
--   Any positive measure on the real line assigning zero mass to the nonpositive halfline has almost-everywhere positive support. This converts P2-B's Proved weighted exponential-image no-nonpositive-mass identity into the exact support premise required by P2-I's moment-to-compact-test theorem.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_i_moment_positive_ae_of_nonpositive_mass_zero
    (μ : Measure ℝ) (hzero : μ (Set.Iic (0 : ℝ)) = 0) :
    ∀ᵐ z ∂μ, 0 < z := by sorry
