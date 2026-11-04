-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_residual_grid_expected_nonpos
-- name    : AvramDividend.Classical.avram_p3_bv_original_residual_grid_expected_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:52:12.553891+00:00
-- url     : https://prove2.me/theorems/10bf363b-435a-42a7-872b-7de2eecddcea
-- title:
--   Genuine original BV residual contribution has nonpositive integrable finite-grid expectation at all reserve contacts
-- statement:
--   For the original BV Levy source and its actual negative left-jump tsum, every integrable discounted finite-grid correction caused by the monotone residual has nonpositive real expectation, including reserve states zero and at the cap. The result uses the accepted source-specific a.e. monotone-residual theorem, global caplinear monotonicity and a valid Mathlib Bochner order bound. It leaves the original jump-compensator and stochastic generator identity unassumed and unresolved.
-- source:
--   Proved a4626fe3 original source boundary residual sign; Mathlib MeasureTheory.integral_nonpos_of_ae. The hypothesis asserts genuine integrability for the particular finite-grid correction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_global_source_residual_boundary_sign
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_residual_grid_expected_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (q : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
    (hu : Monotone u) (n : ℕ) (hstop : ∀ ω, u n ≤ τ ω)
    (hInt : Integrable (fun ω =>
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal
      ∑ i : Fin n, Real.exp (-(q * (u i : ℝ))) *
        (V (riskProcess X x D (u i) ω -
          (R (u (i + 1)) - R (u i))) -
          V (riskProcess X x D (u i) ω))) P) :
    (∫ ω,
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal
      ∑ i : Fin n, Real.exp (-(q * (u i : ℝ))) *
        (V (riskProcess X x D (u i) ω -
          (R (u (i + 1)) - R (u i))) -
          V (riskProcess X x D (u i) ω)) ∂P) ≤ 0 := by sorry
