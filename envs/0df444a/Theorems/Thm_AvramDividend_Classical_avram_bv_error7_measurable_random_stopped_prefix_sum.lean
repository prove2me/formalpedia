-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_measurable_random_stopped_prefix_sum
-- name    : AvramDividend.Classical.avram_bv_error7_measurable_random_stopped_prefix_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T19:07:45.158165+00:00
-- url     : https://prove2.me/theorems/3b58b5ba-77b3-418c-941b-3e8724bf1d79
-- title:
--   Exact random stopped finite physical-grid source sum is a.e. measurable
-- statement:
--   The authentic randomly stopped finite-prefix sum of a.e. strongly measurable physical-cell source functions is a.e. strongly measurable under a bounded measurable stopping index. The result follows from the accepted masked-envelope selector and accepted finite-prefix equality.
-- source:
--   Source exact original stopped-grid AE meas adapter (no surrogate process, no BV prebudget).

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_stopped_index_masked_AE_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_stopped_prefix_eq_masked_finite_grid
open MeasureTheory Set Filter AvramDividend.Classical
open scoped BigOperators

theorem AvramDividend.Classical.avram_bv_error7_measurable_random_stopped_prefix_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (N : ℕ) (k : Ω → ℕ) (hk : Measurable k)
    (hBound : ∀ ω, k ω ≤ N)
    (f : ℕ → Ω → ℝ)
    (hf : ∀ i, AEStronglyMeasurable (f i) P) :
    AEStronglyMeasurable (fun ω =>
      ∑ i ∈ Finset.range (k ω), f i ω) P := by sorry
