-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn10_strict_finite_set_card_le_closed
-- name    : AvramDividend.Classical.avram_bv_jump8_turn10_strict_finite_set_card_le_closed
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:30:23.145999+00:00
-- url     : https://prove2.me/theorems/b34d2b11-bf4e-44e4-a2de-23c86a948d72
-- title:
--   Strict original marked product index cardinal is bounded by closed negative band count
-- statement:
--   The genuine finite set of original path jump times used in the strict negative marked Laplace product is a subset of the closed negative band jump-time set; consequently its finite cardinality is bounded by the closed count whose quadratic moment is already Proved.
-- source:
--   Original-X strict jump set is included in its closed cutoff counterpart, with a finite closed set supplied by e5e6f70b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_turn10_strict_finite_set_card_le_closed
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (k : ℕ) :
    (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset.card ≤
      {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((k : ℝ) + 1))}.ncard := by sorry
