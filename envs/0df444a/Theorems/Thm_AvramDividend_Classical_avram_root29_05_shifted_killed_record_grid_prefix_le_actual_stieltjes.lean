-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_shifted_killed_record_grid_prefix_le_actual_stieltjes
-- name    : AvramDividend.Classical.avram_root29_05_shifted_killed_record_grid_prefix_le_actual_stieltjes
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T15:47:34.583032+00:00
-- url     : https://prove2.me/theorems/4a20d17c-b4ea-4daa-b9ef-bbddac75d841
-- title:
--   Every killed shifted future cash mesh below true stopped Stieltjes payout
-- statement:
--   For each original spectrally negative Lévy sample path, finite shift, nonnegative discount rate, killed clock and positive denominator, every finite grid of sampled future running-record increments has discounted killed cash no greater than the actual strictly stopped Stieltjes dividend payout of that future process.
-- source:
--   On each cell with endpoint before ruin, generic paymentTimes_Ioc_subset_of_terminal_survival and the newly Proved future shifted stopped Stieltjes endpoint bounds give the correct cash inequality. For other cells the sampled cash is zero. Sum via Proved stopped_lintegral_Ioc_partition_fin and monotonicity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_stopped_lintegral_Ioc_partition_fin
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_shifted_stopped_Ioc_discount_record_bounds_of_survival
import Theorems.Thm_AvramDividend_Classical_paymentTimes_Ioc_subset_of_terminal_survival

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- Each finite killed future-record cash mesh is bounded by its true
stopped shifted Stieltjes regulator payout, pathwise. -/

theorem AvramDividend.Classical.avram_root29_05_shifted_killed_record_grid_prefix_le_actual_stieltjes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (age : ℝ≥0)
    (τ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q)
    (n N : ℕ) (hn : 0 < n) :
    let M : ℝ≥0 → ℝ := fun v =>
      sSup ((fun w : ℝ≥0 => X.X (age + w) ω - X.X age ω) '' Icc 0 v)
    let μ : Measure ℝ := dividendMeasure (fun r (_ : Ω) => M r) ω
    let grid : ℕ → ℝ := fun j =>
      (((j : ℝ≥0) * (n : ℝ≥0)⁻¹) : ℝ)
    (∑ k ∈ Finset.range N,
      if ENNReal.ofReal (grid (k + 1)) < τ then
        ENNReal.ofReal (Real.exp (-(q * grid (k + 1)))) *
          ENNReal.ofReal
            (M (grid (k + 1)).toNNReal -
              M (grid k).toNNReal)
      else 0) ≤
    (∫⁻ r in paymentTimes τ,
      if 0 < r then ENNReal.ofReal (Real.exp (-(q * r))) else 0 ∂μ) := by sorry
