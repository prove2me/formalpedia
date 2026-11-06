-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1750_original_full_cutoff_stopped_grid_diagonal_energy
-- name    : AvramDividend.Classical.avram_p4_s3_run1750_original_full_cutoff_stopped_grid_diagonal_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:08:12.814816+00:00
-- url     : https://prove2.me/theorems/f824f223-080a-4c04-9326-4ca19b85909f
-- title:
--   Exact ruin-stopped original negative-jump finite-grid diagonal L2 energy under right-continuous stopping time
-- statement:
--   For a right-continuous stopping time and the genuine original Levy physical negative jumps, the stopped predictable finite-grid compensated count squares are integrable and have an exact diagonal expectation equal to the sum of actual physical intensity times stopped coefficient square expectation.
-- source:
--   Imports the first run1750 accepted original full cutoff finite-grid diagonal isometry and applies the genuine right-continuous filtration stopping-time measurability of {τ≤grid i}.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1750_original_full_cutoff_rightcont_finite_grid_diagonal_energy
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_run1750_original_full_cutoff_stopped_grid_diagonal_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (cut : ℕ)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
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
    let W : ℕ → Ω → ℝ := fun i ω =>
      if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
      then 0 else H i ω
    let Z : ℕ → Ω → ℝ := fun i ω =>
      W i ω * ((N i ω).toReal - r i)
    Integrable (fun ω => ∑ i ∈ Finset.range n, (Z i ω)^2) P ∧
      (∫ ω, ∑ i ∈ Finset.range n, (Z i ω)^2 ∂P) =
        ∑ i ∈ Finset.range n, r i * ∫ ω, (W i ω)^2 ∂P := by sorry
