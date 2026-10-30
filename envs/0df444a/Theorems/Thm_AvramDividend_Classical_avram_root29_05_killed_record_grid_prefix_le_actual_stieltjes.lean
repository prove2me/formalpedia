-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_killed_record_grid_prefix_le_actual_stieltjes
-- name    : AvramDividend.Classical.avram_root29_05_killed_record_grid_prefix_le_actual_stieltjes
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:05:20.828997+00:00
-- url     : https://prove2.me/theorems/94bff3f1-5df3-4cb1-9133-56d400131545
-- title:
--   Finite killed rational record-grid cash is bounded by the genuine stopped reflected Stieltjes dividend reward
-- statement:
--   For any actual spectrally negative Lévy sample path, arbitrary extended drawdown stopping horizon, nonnegative q, positive integer mesh denominator and finite record-grid prefix, retain each discounted running-record increment only when that cell's right endpoint strictly precedes the killing clock. Their sum is bounded by the genuine Stieltjes dividend payout before the stopping horizon, with the positive-time convention. The argument uses the actual regulator and event boundary.
-- source:
--   Proved paymentTimes_Ioc_subset_of_terminal_survival 4256f782, runningSup_stopped_Ioc_discount_record_bounds_of_survival and stopped_lintegral_Ioc_partition_fin. Supports source-faithful reward approximation toward 79978d61.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_stopped_lintegral_Ioc_partition_fin
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_Ioc_discount_record_bounds_of_survival
import Theorems.Thm_AvramDividend_Classical_paymentTimes_Ioc_subset_of_terminal_survival

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.avram_root29_05_killed_record_grid_prefix_le_actual_stieltjes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q)
    (n N : ℕ) (hn : 0 < n) :
    let grid : ℕ → ℝ := fun j =>
      (((j : ℝ≥0) * (n : ℝ≥0)⁻¹) : ℝ)
    (∑ k ∈ Finset.range N,
      if ENNReal.ofReal (grid (k + 1)) < τ then
        ENNReal.ofReal (Real.exp (-(q * grid (k + 1)))) *
          ENNReal.ofReal
            (runningSup X (grid (k + 1)).toNNReal ω -
              runningSup X (grid k).toNNReal ω)
      else 0) ≤
    (∫⁻ r in paymentTimes τ,
      if 0 < r then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) := by sorry
