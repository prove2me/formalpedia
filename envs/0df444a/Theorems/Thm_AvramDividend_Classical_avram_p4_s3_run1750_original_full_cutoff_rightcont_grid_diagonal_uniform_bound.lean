-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1750_original_full_cutoff_rightcont_grid_diagonal_uniform_bound
-- name    : AvramDividend.Classical.avram_p4_s3_run1750_original_full_cutoff_rightcont_grid_diagonal_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:08:12.366673+00:00
-- url     : https://prove2.me/theorems/991ffb4d-82f7-4bfc-ae1e-93e170805c41
-- title:
--   Uniform L2 diagonal budget for physical original negative-cutoff jump grids with bounded predictable coefficients
-- statement:
--   For the genuine original physical negative-jump compensated finite grid, bounded predictable coefficients yield the explicit integrated squared-cell energy upper bound L squared times the sum of actual source intensity rates, with no additional conditional second moment or L2 hypothesis.
-- source:
--   Uses exact accepted original finite-grid diagonal energy and probability-measure integral monotonicity, with physically exact Lévy intensity rates, positivity and bounded predictable coefficients.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1750_original_full_cutoff_rightcont_finite_grid_diagonal_energy
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_run1750_original_full_cutoff_rightcont_grid_diagonal_uniform_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (cut : ℕ)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
    (L : ℝ) (hL : 0 ≤ L) (hBound : ∀ i ω, |H i ω| ≤ L)
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
    (∫ ω, ∑ i ∈ Finset.range n, (Z i ω)^2 ∂P) ≤
      (∑ i ∈ Finset.range n, r i) * L^2 := by sorry
