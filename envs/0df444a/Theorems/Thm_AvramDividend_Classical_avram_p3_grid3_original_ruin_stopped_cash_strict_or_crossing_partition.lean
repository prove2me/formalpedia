-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_cash_strict_or_crossing_partition
-- name    : AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_cash_strict_or_crossing_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:47:59.838439+00:00
-- url     : https://prove2.me/theorems/db7c5004-1bfa-4889-9695-05861dceffaa
-- title:
--   Original stopped physical discounted dividend cash partitions into strictly interior and boundary-crossing cells
-- statement:
--   On the actual original spectrally-negative Levy process X and dividend strategy D, the literal finite stopped-grid Ioc discounted dividendMeasure cash is the sum of strictly interior mesh cells (u(i+1)<tau) plus the only possible boundary-crossing cells (u i<tau and u(i+1)=tau). Post-contact cells carry zero cash by the previously Proved exact original theorem. This is the finite physical-mesh statement that isolates the terminal ruin/horizon atom without assuming w(0)=0 or altering strict Iio T cash.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_physical_cash_zero_after_contact
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_cash_strict_or_crossing_partition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (m n : ℕ) (ω : Ω) (q : ℝ) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun k =>
      min (((min k (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    let cash : ℕ → ℝ := fun i =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal
    (∑ i ∈ Finset.range n, cash i) =
      (∑ i ∈ (Finset.range n).filter
          (fun i => u (i + 1) < τ), cash i) +
      ∑ i ∈ (Finset.range n).filter
        (fun i => u i < τ ∧ u (i + 1) = τ), cash i := by sorry
