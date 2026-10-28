-- Prove2me | Theorems.Thm_AvramDividend_Classical_nat_positive_martingale_finite_grid_maximal_unit_bound
-- name    : AvramDividend.Classical.nat_positive_martingale_finite_grid_maximal_unit_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:48:55.613244+00:00
-- url     : https://prove2.me/theorems/4907ed3a-b6c4-490f-8fbd-c536c0555ef0
-- title:
--   Doob maximal bound at every finite grid for nonnegative unit-mean martingales
-- statement:
--   For any nonnegative real discrete-time martingale of constant unit expectation under a finite measure, the measure of sample paths where its maximum over times zero through n exceeds threshold a, multiplied by a, is at most one. This is the exact finite-grid Doob maximal inequality, intended for the compensated negative Esscher density-ratio martingale and the downward-passage threshold exp(εx).
-- source:
--   Invoke the pinned Mathlib `MeasureTheory.maximal_ineq` for nonnegative submartingales, use `setIntegral_le_integral` to bound the restricted terminal mean by the total unit expectation, and convert the real integral upper bound to ENNReal. The theorem is generic and assumes the genuine fixed-measure martingale; it does not assume that such a process already exists under the finite Esscher law.

import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Data.ENNReal.Real
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.nat_positive_martingale_finite_grid_maximal_unit_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {𝓕 : Filtration ℕ mΩ}
    (Z : ℕ → Ω → ℝ) (hZ : Martingale Z 𝓕 μ)
    (hpos : ∀ n ω, 0 ≤ Z n ω)
    (hunit : ∀ n, (∫ ω, Z n ω ∂μ) = 1)
    (a : ℝ≥0) (n : ℕ) :
    (a : ℝ≥0∞) *
      μ {ω | (a : ℝ) ≤
        (Finset.range (n + 1)).sup'
          (Finset.nonempty_range_add_one) (fun k => Z k ω)} ≤ 1 := by sorry
