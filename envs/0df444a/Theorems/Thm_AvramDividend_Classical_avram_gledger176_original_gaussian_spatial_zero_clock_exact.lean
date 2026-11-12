-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger176_original_gaussian_spatial_zero_clock_exact
-- name    : AvramDividend.Classical.avram_gledger176_original_gaussian_spatial_zero_clock_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T23:09:49.927961+00:00
-- url     : https://prove2.me/theorems/12e1cbe3-44f8-44f0-b346-5f73efb81b13
-- title:
--   Original clipped Gaussian spatial Taylor residual is exactly zero when stopped at time zero
-- statement:
--   For the source-exact Gaussian Taylor residual on the original stopped Lévy path and right-limit dividends, if rho(omega)=0 then every clipped mesh node is zero. The physical first-sum cell increment vanishes identically, and every Gaussian centred and generator Riemann mask is false, including the missing terminal counterterm. This gives the zero-clock event of gledger140 without stochastic moment assumptions.
-- source:
--   Strict boundary-event helper for Open original spatial gledger140 and root-connected gledger50; no independent Brownian or unbounded coefficients.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger176_original_gaussian_spatial_zero_clock_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (ρ : Ω → ℝ≥0) (ω : Ω) (hρ0 : ρ ω = 0) (n m : ℕ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    (∑ i ∈ Finset.range (m + 1),
      E (v (i + 1)) * (w (Z i) - w (Y (v i)))) -
    (∑ i ∈ Finset.range m,
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if s < ρ ω then
        let y := Y s
        let z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
        E s * (deriv w y * z +
          (iteratedDeriv 2 w y / 2) * (z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
      else 0) -
    (∑ i ∈ Finset.range m,
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if s < ρ ω then (Δ : ℝ) * E s * X.generator w (Y s)
      else 0) = 0 := by sorry
