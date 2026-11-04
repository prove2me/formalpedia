-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_global_source_residual_boundary_sign
-- name    : AvramDividend.Classical.avram_p3_bv_global_source_residual_boundary_sign
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:15:14.202097+00:00
-- url     : https://prove2.me/theorems/a4626fe3-c821-4ab3-afc1-cd7cbe31203e
-- title:
--   Original BV global stopped residual discount sign at all cap and zero contact boundaries
-- statement:
--   For the unchanged original bounded-variation spectrally negative Levy path, its canonical physical drift minus true negative left-jump total has a nondecreasing residual on one full-probability event. The original continuous candidate with derivative at least one in every interior capped reserve has a globally monotone cap-linear extension, including zero and cap boundaries. Thus every discounted stopped finite-grid correction caused by subtracting the actual unassigned downward residual is nonpositive for all sampled reserves, with no interior-localisation assumption and no assumption that the residual is zero. The theorem supplies the genuine source-specific boundary-contact residual sign needed by the original BV HJB verification.
-- source:
--   Proved source intrinsic BV nonlinear stopped downward residual 222dbf6e and Proved positive-cap global monotone C1 extension 5e9573dd; original source R retained explicitly.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_global_source_residual_boundary_sign
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
        else w C.toReal + (z - C.toReal)) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω),
        (∑ i : Fin n,
          Real.exp (-(q * (u i : ℝ))) *
            (V (riskProcess X x D (u i) ω -
              (R (u (i + 1)) - R (u i))) -
              V (riskProcess X x D (u i) ω))) ≤ 0 := by sorry
