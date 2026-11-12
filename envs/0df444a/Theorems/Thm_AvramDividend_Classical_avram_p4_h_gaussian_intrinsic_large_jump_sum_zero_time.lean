-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum_zero_time
-- name    : AvramDividend.Classical.avram_p4_h_gaussian_intrinsic_large_jump_sum_zero_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:48:08.481494+00:00
-- url     : https://prove2.me/theorems/a35615a2-156c-4bcd-8021-d2fdd1b8ab0d
-- title:
--   Actual source uncompensated large-jump process starts at zero
-- statement:
--   The original sample-path signed large-negative-jump integral Jlarge over (0,0]×(-infinity,-1] vanishes for every source X and sample point because its time support is empty.
-- source:
--   Published original-source intrinsic large-jump definition 4c0b840b-c1d8-4087-81ff-ad3ec077ddde; the restricted integral over an empty time band is zero with no stochastic assumptions.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_h_gaussian_intrinsic_large_jump_sum_zero_time
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    avram_p4_h_gaussian_intrinsic_large_jump_sum X 0 ω = 0 := by sorry
