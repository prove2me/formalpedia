-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_qDiscount_countable_partition_sum_bounds
-- name    : AvramDividend.Classical.runningSup_qDiscount_countable_partition_sum_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T21:06:10.563953+00:00
-- url     : https://prove2.me/theorems/5233fc65-ce01-48f6-92ff-fc502c21acc6
-- title:
--   Countable actual q-discounted dividend interval rewards lie between endpoint-discounted record sums
-- statement:
--   For nonnegative discount q and any countable sequence of real record observation times, the infinite sum of actual discounted Stieltjes running-supremum dividend rewards on the consecutive half-open intervals is squeezed between the infinite sums of corresponding running-record increments with endpoint exponential discounts. This specialises the remotely proved countable generic antitone-weight bound using the remotely proved antitonicity argument for q-discount. It is a precise input to the subsequent inverse-record Stieltjes discretisation, with no unjustified assertion of killed-record renewal.
-- source:
--   Proved runningSup_discounted_countable_partition_sum_bounds target 1d80dd6e-3eb7-4aeb-98fd-fbc8c9b4f738; Proved runningSup_qDiscount_interval_weight_bounds target 006b3d58-c648-43f8-a16d-8c58934c136e supplies exact antitonicity proof pattern.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_runningSup_discounted_countable_partition_sum_bounds

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_qDiscount_countable_partition_sum_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (q : ℝ) (hq : 0 ≤ q) (u : ℕ → ℝ) :
    (∑' i : ℕ,
        ENNReal.ofReal (Real.exp (-(q * u (i + 1)))) *
          ENNReal.ofReal
            (runningSup X (u (i + 1)).toNNReal ω -
             runningSup X (u i).toNNReal ω)) ≤
      (∑' i : ℕ,
        ∫⁻ r, if r ∈ Set.Ioc (u i) (u (i + 1))
          then ENNReal.ofReal (Real.exp (-(q * r))) else 0
          ∂(dividendMeasure (runningSup X) ω)) ∧
    (∑' i : ℕ,
        ∫⁻ r, if r ∈ Set.Ioc (u i) (u (i + 1))
          then ENNReal.ofReal (Real.exp (-(q * r))) else 0
          ∂(dividendMeasure (runningSup X) ω)) ≤
      (∑' i : ℕ,
        ENNReal.ofReal (Real.exp (-(q * u i))) *
          ENNReal.ofReal
            (runningSup X (u (i + 1)).toNNReal ω -
             runningSup X (u i).toNNReal ω)) := by sorry
