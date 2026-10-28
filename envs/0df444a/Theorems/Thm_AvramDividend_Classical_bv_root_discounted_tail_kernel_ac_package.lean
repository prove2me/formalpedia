-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_root_discounted_tail_kernel_ac_package
-- name    : AvramDividend.Classical.bv_root_discounted_tail_kernel_ac_package
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T18:27:27.72858+00:00
-- url     : https://prove2.me/theorems/6f0d7e31-2588-4069-b0e6-b3872037a991
-- title:
--   Absolutely continuous root-shifted BV Esscher renewal measure kernel
-- statement:
--   At a positive Esscher root in the bounded-variation branch, construct the discounted positive jump-tail renewal measure and retain its absolute continuity with respect to Lebesgue volume, alongside subcritical mass, positive support and its exact positive Laplace transform. This strengthens the canonically proved tail-kernel package by exposing the property required by renewal_measure_ac_on_positive in the finite renewal representation, advancing bv_ac_esscher_scaled_renewal_kernel_series_data towards cstar_lt_top.
-- source:
--   Accepted bv_root_discounted_tail_kernel_package construction, withDensity_absolutelyContinuous, measure restriction null sets.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_root_discounted_tail_kernel_ac_package
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hδ : 0 < X.drift) :
    ∃ (κ : Measure ℝ),
      SFinite κ ∧ κ ≪ volume ∧ κ (Iio (0 : ℝ)) = 0 ∧
      κ Set.univ < ENNReal.ofReal X.drift ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * x))) ∂κ) =
          (∫⁻ z : ℝ≥0,
            ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))) *
              ENNReal.ofReal
                ((1 - Real.exp (-(s * (z : ℝ)))) / s)
              ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y))))) := by sorry
