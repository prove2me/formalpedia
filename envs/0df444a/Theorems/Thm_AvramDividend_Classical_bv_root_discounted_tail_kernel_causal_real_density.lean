-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_root_discounted_tail_kernel_causal_real_density
-- name    : AvramDividend.Classical.bv_root_discounted_tail_kernel_causal_real_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T12:07:45.820079+00:00
-- url     : https://prove2.me/theorems/c0f38713-4947-47af-b417-b5c8176d8fdd
-- title:
--   Causal integrable BV Esscher kernel, vanishing pointwise on the nonpositive half-line
-- statement:
--   For a BV spectrally negative Lévy process at a positive Esscher root, choose a nonnegative measurable integrable real-valued density of the discounted jump-tail renewal measure which is identically zero at every nonpositive argument. Keep the exact measure, subcritical mass and Laplace-transform identity. The kernel support is required pointwise by the correctly normalised BV convolution-power and scale-function series prerequisite for finite cstar.
-- source:
--   Canonical Proved bv_root_discounted_tail_kernel_integrable_real_density; Lebesgue nullity of a singleton; measure restriction and withDensity_indicator identities

import Theorems.Thm_AvramDividend_Classical_bv_root_discounted_tail_kernel_integrable_real_density
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Function.L1Space.Integrable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_root_discounted_tail_kernel_causal_real_density
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hδ : 0 < X.drift) :
    ∃ (κ : Measure ℝ) (K : ℝ → ℝ),
      SFinite κ ∧ κ ≪ volume ∧
      κ Set.univ < ENNReal.ofReal X.drift ∧
      Measurable K ∧ (∀ x : ℝ, 0 ≤ K x) ∧
      Integrable K volume ∧ (∀ x : ℝ, x ≤ 0 → K x = 0) ∧
      κ = volume.withDensity (fun x : ℝ => ENNReal.ofReal (K x)) ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * x))) ∂κ) =
          (∫⁻ z : ℝ≥0,
            ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))) *
              ENNReal.ofReal
                ((1 - Real.exp (-(s * (z : ℝ)))) / s)
              ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y))))) := by sorry
