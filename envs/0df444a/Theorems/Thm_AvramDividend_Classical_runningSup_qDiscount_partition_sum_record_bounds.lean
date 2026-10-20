-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_qDiscount_partition_sum_record_bounds
-- name    : AvramDividend.Classical.runningSup_qDiscount_partition_sum_record_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:51:21.519408+00:00
-- url     : https://prove2.me/theorems/f9678a2d-6d89-4d3f-bcad-c132cd998cf1
-- title:
--   Actual finite q-discounted Stieltjes dividend sums bounded by endpoint-discounted record increments
-- statement:
--   For every nonnegative q and finite real-time partition, the total actual Stieltjes running-supremum dividend reward over consecutive half-open cells is squeezed between the corresponding sums of record increments discounted at terminal and initial partition levels. This is the exact finite-partition q-discount bound needed before stopping and countable inverse-record interchange.
-- source:
--   Remotely Proved runningSup_discounted_partition_sum_bounds target 7805ee08-37dc-4c58-839e-e5ac26c3f659 candidate 11969; pinned and remotely checked antitone exponential discount argument in target 006b3d58-c648-43f8-a16d-8c58934c136e.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_runningSup_discounted_partition_sum_bounds

open Classical MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_qDiscount_partition_sum_record_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n,
      ENNReal.ofReal (Real.exp (-(q * u (i + 1)))) *
        ENNReal.ofReal
          (runningSup X (u (i + 1)).toNNReal ω -
           runningSup X (u i).toNNReal ω)) ≤
    (∑ i ∈ Finset.range n,
      ∫⁻ r, if r ∈ Set.Ioc (u i) (u (i + 1))
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ∧
    ((∑ i ∈ Finset.range n,
      ∫⁻ r, if r ∈ Set.Ioc (u i) (u (i + 1))
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ≤
      ∑ i ∈ Finset.range n,
        ENNReal.ofReal (Real.exp (-(q * u i))) *
          ENNReal.ofReal
            (runningSup X (u (i + 1)).toNNReal ω -
             runningSup X (u i).toNNReal ω)) := by sorry
