-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a418_original_Gaussian_crossing_scalar_fullcell_quadratic_bound
-- name    : AvramDividend.Classical.avram_ga_a418_original_Gaussian_crossing_scalar_fullcell_quadratic_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:33:48.804798+00:00
-- url     : https://prove2.me/theorems/7298e76a-79db-4d84-bcb1-e680c1f52217
-- title:
--   Original stopped Gaussian HJB percell absolute term has uniform quadratic source bound
-- statement:
--   Uniform compact pre-stop C2 and Gaussian generator coefficient bounds yield a common deterministic multiple of the absolute centred fullcell Gaussian increment, its square and mesh width, controlling each original discounted compensated HJB cell.
-- source:
--   Proved a396 original Gaussian C2+generator coefficients and a398 scalar HJB quadratic inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a418_original_Gaussian_crossing_scalar_fullcell_quadratic_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᵐ ω ∂P, ∀ m i : ℕ,
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let y : ℝ := x + X.X s ω - rightLimit D s ω
        let z : ℝ := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
        s < ρ ω →
          |Real.exp (-(q * (s : ℝ))) *
              (deriv w y * z + (iteratedDeriv 2 w y / 2) *
                (z^2 - (Δ : ℝ) * X.σ^2)) +
            (Δ : ℝ) * Real.exp (-(q * (s : ℝ))) *
              X.generator w y| ≤
          K * (|z| + z^2 + (Δ : ℝ)) := by sorry
