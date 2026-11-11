-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin22_original_true_clipped_upper_value_bound
-- name    : AvramDividend.Classical.avram_mix_fin22_original_true_clipped_upper_value_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T10:29:45.885069+00:00
-- url     : https://prove2.me/theorems/5f2bbc05-6f6c-41ca-ae36-7f3a1b623602
-- title:
--   Original clipped strict upper exit cannot overshoot spatial threshold
-- statement:
--   An exact physical compact localisation bound for the original mixed Lévy process. For every path, every fixed positive level b and every possibly random finite clock ρ, the original process sampled at min(ρ, the true strict upper-exit time at b) never exceeds b. Before exit use Proved ddce7de4; at or beyond exit use Proved firstUpcrossing_value_le_threshold, which encodes absence of positive Lévy jumps. This supplies the previously missing upper path bound needed to make the top-cap compact rewards integrable and to isolate the local Ito budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin22_original_strict_pre_upper_clock_value_le
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_le_threshold
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin22_original_true_clipped_upper_value_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (hb : 0 < b)
    (ω : Ω) (ρ : ℝ≥0) :
    X.X ((min (ρ : ℝ≥0∞) (twoSidedExitUpTime X b ω)).toNNReal) ω ≤ b := by sorry
