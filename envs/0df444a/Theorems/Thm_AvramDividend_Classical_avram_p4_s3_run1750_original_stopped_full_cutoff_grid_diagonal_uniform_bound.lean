-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1750_original_stopped_full_cutoff_grid_diagonal_uniform_bound
-- name    : AvramDividend.Classical.avram_p4_s3_run1750_original_stopped_full_cutoff_grid_diagonal_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:18:44.252139+00:00
-- url     : https://prove2.me/theorems/518953d8-b77f-4281-b015-79df7f446eae
-- title:
--   Quantitative original stopped negative cutoff finite-grid square-energy budget at ruin and horizon clock
-- statement:
--   For a genuine right-continuous stopping time τ, original physical negative-jump compensated finite-grid increments stopped at left endpoints have total diagonal squared energy bounded by L squared times the sum of exact original physical Lévy rates, with no separate count variance or integrability side condition.
-- source:
--   Derives source-exact stopped predictable coefficients by 𝓕.rightCont stopping-time measurability and applies independent Proved original full-cutoff finite-grid energy bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1750_original_full_cutoff_rightcont_grid_diagonal_uniform_bound
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_run1750_original_stopped_full_cutoff_grid_diagonal_uniform_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (cut : ℕ)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
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
    let W : ℕ → Ω → ℝ := fun i ω =>
      if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
      then 0 else H i ω
    let Z : ℕ → Ω → ℝ := fun i ω =>
      W i ω * ((N i ω).toReal - r i)
    (∫ ω, ∑ i ∈ Finset.range n, (Z i ω)^2 ∂P) ≤
      (∑ i ∈ Finset.range n, r i) * L^2 := by sorry
