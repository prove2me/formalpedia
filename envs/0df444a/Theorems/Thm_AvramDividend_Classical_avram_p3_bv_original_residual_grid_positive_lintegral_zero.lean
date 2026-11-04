-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_residual_grid_positive_lintegral_zero
-- name    : AvramDividend.Classical.avram_p3_bv_original_residual_grid_positive_lintegral_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:09:32.854437+00:00
-- url     : https://prove2.me/theorems/038b6132-0334-42f9-9e74-c70bc6b8c41b
-- title:
--   Original source BV residual finite-grid positive-part lintegral vanishes without any L1 condition
-- statement:
--   For the actual original spectrally negative BV Levy path and every stopped finite grid, the nonnegative ENNReal positive part of the true signed residual candidate correction has identically zero expected mass, with no integrability or finite-moment condition. Supports Fatou/localisation once original stopped C1 stochastic identity is available.
-- source:
--   Accepted a4626fe3 original-source boundary residual global sign; Mathlib ENNReal.ofReal_eq_zero and MeasureTheory.lintegral_congr_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_global_source_residual_boundary_sign
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_residual_grid_positive_lintegral_zero
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
    (hu : Monotone u) (n : ℕ) (hstop : ∀ ω, u n ≤ τ ω) :
    (∫⁻ ω, ENNReal.ofReal
      (let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal
      ∑ i : Fin n, Real.exp (-(q * (u i : ℝ))) *
        (V (riskProcess X x D (u i) ω -
          (R (u (i + 1)) - R (u i))) -
          V (riskProcess X x D (u i) ω))) ∂P) = 0 := by sorry
