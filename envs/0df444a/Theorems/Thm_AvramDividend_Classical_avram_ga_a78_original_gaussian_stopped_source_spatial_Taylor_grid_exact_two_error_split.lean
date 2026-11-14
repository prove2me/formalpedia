-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a78_original_gaussian_stopped_source_spatial_Taylor_grid_exact_two_error_split
-- name    : AvramDividend.Classical.avram_ga_a78_original_gaussian_stopped_source_spatial_Taylor_grid_exact_two_error_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:45:09.072196+00:00
-- url     : https://prove2.me/theorems/a06cb088-3edb-40dc-8d4a-368d8320f1e9
-- title:
--   Original true-stop physical Gaussian compensated source spatial generator finite grid splits into exact classical Taylor remainder and drift cross quadratic error
-- statement:
--   For the actual original zero-jump Levy driver, its genuine dividend process and the actual stop-selected finite physical Gaussian grid, the spatial source increment minus centred Gaussian linear and quadratic terms and generator is exactly the sum of the classical spatial C2 Taylor remainder and raw-versus-centred quadratic cross error.
-- source:
--   Direct sound b0d9951c original Gaussian positive-only stopped interior spatial compensated Taylor exact decomposition; uses ga_a77.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a78_original_gaussian_stopped_source_spatial_Taylor_grid_exact_two_error_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ)
    (ρ : Ω → ℝ≥0) (ω : Ω) (S : Finset ℕ)
    (s : ℕ → ℝ≥0) (Δ : ℝ≥0) :
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℕ → ℝ := fun i =>
      x + X.X (s i) ω - rightLimit D (s i) ω
    let R : ℕ → ℝ := fun i =>
      X.X (s i + Δ) ω - X.X (s i) ω
    let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
    (∑ i ∈ S, if s i < ρ ω then
      E (s i) * (w (Y i + R i) - w (Y i) -
        (deriv w (Y i) * Z i +
          (iteratedDeriv 2 w (Y i) / 2) *
            (Z i^2 - (Δ : ℝ) * X.σ^2)) -
        (Δ : ℝ) * X.generator w (Y i))
      else 0) =
    (∑ i ∈ S, if s i < ρ ω then
      E (s i) * (w (Y i + R i) - w (Y i) -
        deriv w (Y i) * R i -
        (iteratedDeriv 2 w (Y i) / 2) * R i^2)
      else 0) +
    (∑ i ∈ S, if s i < ρ ω then
      E (s i) * (iteratedDeriv 2 w (Y i) / 2) *
        (R i^2 - Z i^2)
      else 0) := by sorry
