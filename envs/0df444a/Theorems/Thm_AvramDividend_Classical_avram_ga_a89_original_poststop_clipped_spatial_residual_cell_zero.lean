-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a89_original_poststop_clipped_spatial_residual_cell_zero
-- name    : AvramDividend.Classical.avram_ga_a89_original_poststop_clipped_spatial_residual_cell_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:11:40.376765+00:00
-- url     : https://prove2.me/theorems/9ffaf554-4598-46fb-bf3d-bb7df84d14f7
-- title:
--   Every post-stop original Gaussian physical source cell has identically zero clipped spatial and generator residual
-- statement:
--   For the actual original dividend-controlled Gaussian process, on any physical cell beginning at or after the true stopping clock, the entire clipped spatial value increment and masked Gaussian generator-compensator residual are exactly zero.
-- source:
--   Direct b0d9951c exact original true stopped source classification; complements ga_a71 full and ga_a72 crossing cells.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a89_original_poststop_clipped_spatial_residual_cell_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (ω : Ω) (n m i : ℕ) (ρ : ℝ≥0)
    (hpost : let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ρ ≤ (i : ℝ≥0) * Δ) :
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
      = 0 := by sorry
