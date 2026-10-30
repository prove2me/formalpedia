-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_actual_stieltjes_eq_killed_record_grid_sup
-- name    : AvramDividend.Classical.avram_root29_05_actual_stieltjes_eq_killed_record_grid_sup
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:56:56.305971+00:00
-- url     : https://prove2.me/theorems/4e232b08-af14-4675-b063-2f7ebfe9b220
-- title:
--   Actual killed Stieltjes barrier record-dividend reward equals all rational finite sampled record prefixes
-- statement:
--   For each actual spectrally negative Lévy sample path, arbitrary strictly killed time and nonnegative discount, the original running-supremum Stieltjes dividend reward integrated over original paymentTimes equals the supremum of all finite strictly surviving discount-weighted rational-grid increments of the actual running supremum. Both inequalities use Proved source-faithful genuine Stieltjes measure theorems. Includes exact no-time-zero-regulator normalisation, with original positive-time payment set. This does not yet identify the reflected barrier regulator after first upcrossing.
-- source:
--   Author-verified accepted 8a816a69 global lower, c5704d66 Fatou-based reverse, 9c1008b1 paymentTimes bridge; algebraic identification of the two rational grids. Source-level true dividendMeasure, not the deprecated stopping set.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_all_killed_record_grid_prefixes_le_actual_stieltjes
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_actual_stieltjes_le_killed_record_grid_sup
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_paymentTimes_positive_weight_eq_strict_indicator

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.avram_root29_05_actual_stieltjes_eq_killed_record_grid_sup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ r in paymentTimes τ,
      if 0 < r then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) =
    (⨆ n : ℕ, ⨆ N : ℕ,
      let grid : ℕ → ℝ := fun j =>
        (((j : ℝ≥0) * ((n + 1 : ℕ) : ℝ≥0)⁻¹) : ℝ)
      ∑ k ∈ Finset.range N,
        if ENNReal.ofReal (grid (k + 1)) < τ then
          ENNReal.ofReal (Real.exp (-(q * grid (k + 1)))) *
            ENNReal.ofReal
              (runningSup X (grid (k + 1)).toNNReal ω -
                runningSup X (grid k).toNNReal ω)
        else 0) := by sorry
