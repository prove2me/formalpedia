-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_any_cofinal_halfband_zero_shifted_candidate_increment_tendsto_zero
-- name    : AvramDividend.Classical.avram_bva_a22_original_any_cofinal_halfband_zero_shifted_candidate_increment_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:06:39.624689+00:00
-- url     : https://prove2.me/theorems/c40cb52a-8591-4ad8-a243-898326808ab2
-- title:
--   Original arbitrary cofinal half-band zero-shifted candidate value increment converges to zero at the actual source widths
-- statement:
--   Given any strictly positive cap in the original dividend verification model, any original candidate w continuous on all nonnegative reserve levels and any arbitrary original cofinal reserve bands a_n,b_n satisfying positive lower widths and eventual coverage of every strict interior reserve, prove that w(a_n/2)-w(0) converges to zero. The Proved original cofinal lower-band theorem gives a_n to zero with no nesting or prescribed spatial/physical mesh rate. The literal half-band a_n/2 remains nonnegative, so compose the restricted continuity of w at the reserve zero with convergence to zero along the right-hand side. This establishes that the original deterministic zero-shifted negative-mark boundary error envelope in the stopped infinite-activity BV C1 calculation vanishes even when w(0) is positive, leaving the possible isolated actual ruin-crossing charge accounted for separately.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_arbitrary_cofinal_positive_spatial_lower_band_tendsto_zero_without_rate
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_any_cofinal_halfband_zero_shifted_candidate_increment_tendsto_zero
    (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici (0 : ℝ)))
    (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (hab : ∀ n, a n ≤ b n)
    (hinside : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hcover : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n)) :
    Tendsto (fun n => w (a n / 2) - w 0)
      atTop (𝓝 (0 : ℝ)) := by sorry
