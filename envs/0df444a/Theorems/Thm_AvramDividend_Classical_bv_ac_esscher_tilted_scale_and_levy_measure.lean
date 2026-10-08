-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_ac_esscher_tilted_scale_and_levy_measure
-- name    : AvramDividend.Classical.bv_ac_esscher_tilted_scale_and_levy_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:19:16.917783+00:00
-- url     : https://prove2.me/theorems/0e5238b7-acb6-49c8-9c09-c04384c6f2c0
-- title:
--   Construct analytic tilted zero-scale transform and absolutely continuous tilted Lévy measure
-- statement:
--   The Esscher transform of the Lévy measure stays supported on negative jumps, absolutely continuous, and Lévy-integrable; V(x)=exp(-φx)W(x) is related to W by the Esscher exponential and has the shifted Laplace transform whenever ψ(θ+φ)>q. This makes the zero-discount tilted model available analytically without constructing its excursion measure. The two inputs are existing Proved esscher_bv_ac_levy_package and esscher_tilted_scale_laplace_shift.
-- source:
--   Chan, Kyprianou and Savov (2011), equation (3) Lévy measure tilt and equation (4) scale tilt; canonical X.ψ definition and Proved transfer facts.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_ac_esscher_tilted_scale_and_levy_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hac : X.ν ≪ volume)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ V : ℝ → ℝ,
      (X.ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y)))) (Ici 0) = 0 ∧
      (X.ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y)))) ≪ volume ∧
      (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2))
        ∂(X.ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))) < ⊤ ∧
      (∀ x : ℝ, W x = Real.exp (φ * x) * V x) ∧
      (∀ θ : ℝ, 0 ≤ θ + φ → q < X.ψ (θ + φ) →
        IntegrableOn (fun y : ℝ => Real.exp (-(θ * y)) * V y) (Ioi 0) volume ∧
        (∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) * V y ∂volume) =
        (X.ψ (θ + φ) - q)⁻¹) := by sorry
