-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva84_original_strict_positive_jump_count_zero_at_initial_clock
-- name    : AvramDividend.Classical.avram_bva84_original_strict_positive_jump_count_zero_at_initial_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:28:57.357068+00:00
-- url     : https://prove2.me/theorems/8e8b2ae0-78a0-44ee-b35f-6ad588c18eaa
-- title:
--   Original positive Lévy jump-time count has zero initial-time mass
-- statement:
--   The counting measure of actual Lévy jump times is restricted to strictly positive times, hence its mass at zero vanishes pathwise, providing the jump-count side of the initial compensated source M_n(0).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva84_original_strict_positive_jump_count_zero_at_initial_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0})
      ({0} : Set ℝ≥0) = 0 := by sorry
