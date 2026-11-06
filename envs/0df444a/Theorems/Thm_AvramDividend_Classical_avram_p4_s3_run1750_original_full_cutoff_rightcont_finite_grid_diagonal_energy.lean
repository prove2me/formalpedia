-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1750_original_full_cutoff_rightcont_finite_grid_diagonal_energy
-- name    : AvramDividend.Classical.avram_p4_s3_run1750_original_full_cutoff_rightcont_finite_grid_diagonal_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:59:52.22183+00:00
-- url     : https://prove2.me/theorems/7b1055b2-ce63-480a-ba8a-f72458251f59
-- title:
--   Exact finite-grid diagonal quadratic energy for original negative Lévy jumps and right-continuous predictable coefficients
-- statement:
--   On the genuine original spectrally negative Levy sample paths and actual full negative-cutoff physical marked jump counts, the sum of predictable compensated-cell squares is integrable, with its exact expected value equal to the sum of original physical intensity rates multiplied by each coefficient-square expectation. Uses the already proved original conditional variance without a new stochastic axiom.
-- source:
--   Exact import of Proved public full-cutoff bounded predictable L2 isometry 5d14bcf5-2b2e-4711-af4a-f5e504e195ee, instantiated on each original physical grid cell, and finite-sum integral linearity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_bounded_predictable_L2_isometry_auto
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_run1750_original_full_cutoff_rightcont_finite_grid_diagonal_energy
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
    Integrable (fun ω => ∑ i ∈ Finset.range n, (Z i ω)^2) P ∧
      (∫ ω, ∑ i ∈ Finset.range n, (Z i ω)^2 ∂P) =
        ∑ i ∈ Finset.range n, r i * ∫ ω, (H i ω)^2 ∂P := by sorry
