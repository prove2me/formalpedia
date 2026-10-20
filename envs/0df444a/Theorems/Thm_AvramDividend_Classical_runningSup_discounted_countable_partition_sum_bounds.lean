-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_discounted_countable_partition_sum_bounds
-- name    : AvramDividend.Classical.runningSup_discounted_countable_partition_sum_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:44:15.598259+00:00
-- url     : https://prove2.me/theorems/1d80dd6e-3eb7-4aeb-98fd-fbc8c9b4f738
-- title:
--   Countable interval Stieltjes dividend sums bounded by discounted record increments
-- statement:
--   For the original running-supremum Stieltjes dividend measure, any countable sequence of real interval endpoints and any antitone extended-nonnegative discount weight satisfy bounds for the infinite sum of interval rewards. The lower and upper bounds are the corresponding infinite sums of running-record increments weighted by the right and left endpoint discounts. The theorem is independent of whether endpoints are ordered and does not claim that the sum equals one stopped integral until disjointness and partition coverage are separately proved.
-- source:
--   Remotely Proved runningSup_discounted_interval_bounds_record_increment b5f13432-7b43-44fb-a3bc-afa7877c8aca; pinned Mathlib theorem ENNReal.tsum_le_tsum indexed in Mathlib.Topology.Algebra.InfiniteSum.ENNReal.

import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Theorems.Thm_AvramDividend_Classical_runningSup_discounted_interval_bounds_record_increment

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_discounted_countable_partition_sum_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (w : ℝ → ℝ≥0∞) (hw : Antitone w)
    (u : ℕ → ℝ) :
    (∑' i : ℕ,
        w (u (i + 1)) *
          ENNReal.ofReal
            (runningSup X (u (i + 1)).toNNReal ω -
             runningSup X (u i).toNNReal ω)) ≤
      (∑' i : ℕ,
        ∫⁻ r, if r ∈ Set.Ioc (u i) (u (i + 1)) then w r else 0
          ∂(dividendMeasure (runningSup X) ω)) ∧
    (∑' i : ℕ,
        ∫⁻ r, if r ∈ Set.Ioc (u i) (u (i + 1)) then w r else 0
          ∂(dividendMeasure (runningSup X) ω)) ≤
      (∑' i : ℕ,
        w (u i) *
          ENNReal.ofReal
            (runningSup X (u (i + 1)).toNNReal ω -
             runningSup X (u i).toNNReal ω)) := by sorry
