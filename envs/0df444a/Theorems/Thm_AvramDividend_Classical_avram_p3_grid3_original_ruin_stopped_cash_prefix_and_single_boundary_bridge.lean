-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_cash_prefix_and_single_boundary_bridge
-- name    : AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_cash_prefix_and_single_boundary_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:13:58.94405+00:00
-- url     : https://prove2.me/theorems/45592cc1-af59-4076-bcc9-e791c065e505
-- title:
--   Original stopped discounted cash equals exact strict-prefix cash plus the sole crossing-cell term
-- statement:
--   On the literal original spectrally-negative Levy process X and actual admissible strategy D, for every physical ruin/horizon-stopped uniform grid choose k≤m+1 so full paymentTimes∩Ioc discounted dividendMeasure cash equals strict-prefix sum range k plus the boundary-crossing filter. Whenever tau>0, the prefix terminal u k lies strictly before tau, allowing the existing Proved full signed Stieltjes prefix source budgets to apply. Uniqueness of the crossing cell is already separately Proved. This is a necessary exact cash decomposition towards the Fatou source certificate, with no added stochastic or terminal hypotheses.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_cash_strict_or_crossing_partition
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_strict_prefix_terminal_below_tau
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_cash_prefix_and_single_boundary_bridge
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
    ∃ k : ℕ, k ≤ m + 1 ∧
      ((∑ i ∈ Finset.range (m + 1), cash i) =
        (∑ i ∈ Finset.range k, cash i) +
        ∑ i ∈ (Finset.range (m + 1)).filter
          (fun i => u i < τ ∧ u (i + 1) = τ), cash i) ∧
      (0 < τ → u k < τ) := by sorry
