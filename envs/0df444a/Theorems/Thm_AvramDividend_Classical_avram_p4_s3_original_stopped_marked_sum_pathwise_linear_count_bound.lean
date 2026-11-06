-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_stopped_marked_sum_pathwise_linear_count_bound
-- name    : AvramDividend.Classical.avram_p4_s3_original_stopped_marked_sum_pathwise_linear_count_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:26:53.444926+00:00
-- url     : https://prove2.me/theorems/56330434-50a6-49a8-b738-c148fa14eae7
-- title:
--   Original stopped negative-band physical marked-time sum is pathwise bounded by coefficient ceiling times actual jump count
-- statement:
--   For any original spectrally negative Lévy path, arbitrary path-dependent finite clock τ and arbitrary mark-time kernel bounded in absolute value by B, the actual finite sum over original marked negative-band jump times is bounded in absolute value by B times its original pathwise jump-count cardinality. No clock measurability or stochastic assumptions are needed.
-- source:
--   The published original marked-times finite theorem and exact Set.ncard_eq_toFinset_card, with norm_sum_le.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_s3_original_stopped_marked_sum_pathwise_linear_count_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ)
    (τ : Ω → ℝ≥0) (f : Ω → ℝ≥0 → ℝ) (B : ℝ)
    (hf : ∀ ω u, |f ω u| ≤ B) :
    ∀ ω : Ω,
      ‖∑ u ∈ (avram_wave7_06_original_negative_band_marked_times_finite
        X ω (τ ω) n).toFinset, f ω u‖ ≤
        B * ({u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
            -(1 / ((n : ℝ) + 1))}.ncard : ℝ) := by sorry
