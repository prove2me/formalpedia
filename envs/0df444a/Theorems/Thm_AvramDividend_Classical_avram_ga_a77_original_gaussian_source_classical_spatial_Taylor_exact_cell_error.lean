-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a77_original_gaussian_source_classical_spatial_Taylor_exact_cell_error
-- name    : AvramDividend.Classical.avram_ga_a77_original_gaussian_source_classical_spatial_Taylor_exact_cell_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:44:39.04819+00:00
-- url     : https://prove2.me/theorems/f6a2c64b-96d6-4644-8a35-295ab20f6d80
-- title:
--   Exact original Gaussian full physical cell generator residual equals classical C2 spatial Taylor remainder plus raw-centred cross quadratic error
-- statement:
--   For the actual zero-jump Levy source X and cumulative dividend D on any original physical time cell, the discounted original spatial value increment minus centred Gaussian first and second order source terms and physical HJB generator drift equals the ordinary raw-source Taylor error plus one half the Hessian times the raw-versus-centred square difference.
-- source:
--   Direct b0d9951c positive-only original Gaussian stopped interior spatial compensated mesh source algebra, isolate classical C2 error and quadratic cross drift.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a77_original_gaussian_source_classical_spatial_Taylor_exact_cell_error
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ)
    (ω : Ω) (s Δ : ℝ≥0) :
    let E : ℝ := Real.exp (-(q * (s : ℝ)))
    let y : ℝ := x + X.X s ω - rightLimit D s ω
    let r : ℝ := X.X (s + Δ) ω - X.X s ω
    let z : ℝ := r - (Δ : ℝ) * X.c
    E * (w (y + r) - w y -
      (deriv w y * z +
        (iteratedDeriv 2 w y / 2) * (z^2 - (Δ : ℝ) * X.σ^2)) -
      (Δ : ℝ) * X.generator w y) =
    E * (w (y + r) - w y -
      deriv w y * r - (iteratedDeriv 2 w y / 2) * r^2) +
      E * (iteratedDeriv 2 w y / 2) * (r^2 - z^2) := by sorry
