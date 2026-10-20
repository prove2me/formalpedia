-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_discounted_partition_sum_bounds
-- name    : AvramDividend.Classical.runningSup_discounted_partition_sum_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:28:02.424802+00:00
-- url     : https://prove2.me/theorems/7805ee08-37dc-4c58-839e-e5ac26c3f659
-- title:
--   Finite Stieltjes payout partition bounded by discounted running-supremum increments
-- statement:
--   For any deterministic finite sequence of real observation times and any antitone ENNReal discount weight, the sum of actual discounted Stieltjes regulator payouts over consecutive half-open intervals is bounded below and above by the corresponding sums of record increases with discount weights taken at the interval endpoints. The inequalities remain valid for nonordered times because the already Proved per-interval inequalities hold for arbitrary real endpoints. This is a finite-partition precursor to the countable stopped-regulator payout decomposition.
-- source:
--   Proved runningSup_discounted_interval_bounds_record_increment b5f13432-7b43-44fb-a3bc-afa7877c8aca; pinned Finset.sum_le_sum confirmed in Mathlib.Algebra.Order.BigOperators.Group.Finset.

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Theorems.Thm_AvramDividend_Classical_runningSup_discounted_interval_bounds_record_increment

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_discounted_partition_sum_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (w : ℝ → ℝ≥0∞) (hw : Antitone w)
    (u : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n,
        w (u (i + 1)) *
          ENNReal.ofReal
            (runningSup X (u (i + 1)).toNNReal ω -
             runningSup X (u i).toNNReal ω)) ≤
      (∑ i ∈ Finset.range n,
        ∫⁻ r, if r ∈ Set.Ioc (u i) (u (i + 1)) then w r else 0
          ∂(dividendMeasure (runningSup X) ω)) ∧
    (∑ i ∈ Finset.range n,
        ∫⁻ r, if r ∈ Set.Ioc (u i) (u (i + 1)) then w r else 0
          ∂(dividendMeasure (runningSup X) ω)) ≤
      (∑ i ∈ Finset.range n,
        w (u i) *
          ENNReal.ofReal
            (runningSup X (u (i + 1)).toNNReal ω -
             runningSup X (u i).toNNReal ω)) := by sorry
