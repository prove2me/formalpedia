-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a90_original_stop_crossing_gaussian_spatial_generator_residual_exact
-- name    : AvramDividend.Classical.avram_ga_a90_original_stop_crossing_gaussian_spatial_generator_residual_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:11:52.885112+00:00
-- url     : https://prove2.me/theorems/40481b79-424b-494d-b0ec-b3376b254b33
-- title:
--   Original Gaussian stop-straddling source spatial residual uses true stopped value endpoint and full physical compensated generator clock
-- statement:
--   For the unique physical Gaussian source cell starting strictly before the real stopping clock rho but ending after it, the actual stopped spatial HJB residual has a true stopped source value increment and the full source Gaussian deterministic physical compensator and generator, with exact algebraic equality.
-- source:
--   Direct b0d9951c source-exact true stopping-crossing cell needed for positive L1, uses proved ga_a72.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a90_original_stop_crossing_gaussian_spatial_generator_residual_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (ω : Ω) (n m i : ℕ) (ρ : ℝ≥0)
    (hstart : let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (i : ℝ≥0) * Δ < ρ)
    (hend : let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ρ ≤ (i : ℝ≥0) * Δ + Δ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) ρ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t =>
      x + X.X t ω - rightLimit D t ω
    let Z : ℝ := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
    E (v (i + 1)) *
      (w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω) -
        w (Y (v i))) -
      (if s < ρ then E s * (deriv w (Y s) * Z +
        (iteratedDeriv 2 w (Y s) / 2) *
          (Z^2 - (Δ : ℝ) * X.σ^2)) else 0) -
      (if s < ρ then (Δ : ℝ) * E s * X.generator w (Y s) else 0)
      =
    E ρ * (w (Y s + (X.X ρ ω - X.X s ω)) - w (Y s)) -
      E s * (deriv w (Y s) * Z +
        (iteratedDeriv 2 w (Y s) / 2) *
          (Z^2 - (Δ : ℝ) * X.σ^2)) -
      (Δ : ℝ) * E s * X.generator w (Y s) := by sorry
