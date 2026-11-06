-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_cash_prefix_plus_unique_crossing_cell
-- name    : AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_cash_prefix_plus_unique_crossing_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:23:40.057532+00:00
-- url     : https://prove2.me/theorems/da4ca373-4176-44d2-b145-d9ec3456900c
-- title:
--   Original positive-time stopped physical cash equals exact strict interior prefix plus one actual crossing cell
-- statement:
--   Combine the already Proved original stopped-grid exact cash prefix/crossing partition with the actual-process positive-time unique-crossing singleton. For every positive stopped time, the entire finite original dividendMeasure physical cash sum equals the strict-pre-ruin prefix cash plus precisely one last crossing cell cash. The source is literally the original X, D, its ruinTime, time-zero and ENNReal-discounted Stieltjes integrals. This identifies the finite cash boundary that must be treated separately under strict Iio T versus closed Iic T at a surviving horizon.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_cash_prefix_and_single_boundary_bridge
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_positive_tau_boundary_filter_singleton
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_cash_prefix_plus_unique_crossing_cell
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (m : ℕ) (ω : Ω) (q : ℝ) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    let cash : ℕ → ℝ := fun i =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal
    0 < τ →
      ∃ k i : ℕ, k ≤ m + 1 ∧ u k < τ ∧
        i < m + 1 ∧ u i < τ ∧ u (i + 1) = τ ∧
        (∑ j ∈ Finset.range (m + 1), cash j) =
          (∑ j ∈ Finset.range k, cash j) + cash i := by sorry
