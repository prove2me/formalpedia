-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_native_esscher_root_volterra_denominator
-- name    : AvramDividend.Classical.gaussian_native_esscher_root_volterra_denominator
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T14:43:50.841043+00:00
-- url     : https://prove2.me/theorems/940fe5d7-57a3-4d9e-8fcb-89cac9df91e5
-- title:
--   Native Gaussian Esscher q-resolvent Volterra denominator without extra measure assumptions
-- statement:
--   The Gaussian Esscher-shift Volterra denominator identity holds directly under the native spectrally negative Lévy conditions, with no separately assumed positive-magnitude Lévy truncation. The native truncated-square moment is restricted to negative jumps, transported through sign pushforward, and passed to the previously proved native-exponent identity.
-- source:
--   Derived from proved gaussian_levy_square_integrable_neg_pushforward and proved gaussian_esscher_psi_volterra_denominator_of_root.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_square_integrable_neg_pushforward
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_psi_volterra_denominator_of_root
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.gaussian_native_esscher_root_volterra_denominator
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ θ : ℝ) (hφ : 0 < φ) (hθ : 0 ≤ θ) (hroot : X.ψ φ = q) :
    X.ψ (φ + θ) - q =
      θ * (X.c - (X.ν.map (fun y : ℝ => -y)).real ({1} : Set ℝ) +
        X.σ ^ 2 * φ +
        (∫ z in Ioi (0 : ℝ),
          (if z ≤ 1 then z else 0) - z * Real.exp (-φ * z)
          ∂(X.ν.map (fun y : ℝ => -y)))) +
      (X.σ ^ 2 / 2) * θ ^ 2 +
      (∫ z in Ioi (0 : ℝ),
        Real.exp (-φ * z) *
          (Real.exp (-θ * z) - 1 + θ * z)
        ∂(X.ν.map (fun y : ℝ => -y))) := by sorry
