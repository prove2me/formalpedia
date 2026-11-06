-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_predictable_finite_grid_L2_zero_mean
-- name    : AvramDividend.Classical.avram_p4_s3_interval_h_original_full_cutoff_predictable_finite_grid_L2_zero_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:35:47.216177+00:00
-- url     : https://prove2.me/theorems/06c6a15a-7bda-4a40-b822-6d070aab8286
-- title:
--   Real original physical full negative-cutoff predictable finite-grid L² compensated martingale and zero mean
-- statement:
--   For actual original Lévy X and real P/ν, any nondecreasing finite deterministic time grid and bounded right-continuously predictable coefficients H_i, the physical full-negative-cutoff compensated marked jump count grid sum is L² and has exactly zero terminal expectation, without external moment or isometry assumptions, with a finite-cutoff and finite-grid scope.
-- source:
--   Each full-cutoff actual physical marked-count cell satisfies the independently Proved automatic bounded predictable conditional martingale step. A finite sum of L² cells remains L² and has zero expectation by linearity. The source time grid identity uses add_tsub_cancel_of_le.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_bounded_weight_conditional_martingale_step
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_h_original_full_cutoff_predictable_finite_grid_L2_zero_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (cut : ℕ)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
    (L : ℝ) (hBound : ∀ i ω, |H i ω| ≤ L)
    (n : ℕ) :
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
    let r : ℕ → ℝ := fun i =>
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
    let Z : ℕ → Ω → ℝ := fun i ω =>
      H i ω * ((N i ω).toReal - r i)
    MemLp (fun ω => ∑ i ∈ Finset.range n, Z i ω) 2 P ∧
    (∫ ω, ∑ i ∈ Finset.range n, Z i ω ∂P) = 0 := by sorry
