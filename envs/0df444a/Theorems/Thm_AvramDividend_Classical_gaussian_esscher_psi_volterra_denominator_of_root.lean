-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_psi_volterra_denominator_of_root
-- name    : AvramDividend.Classical.gaussian_esscher_psi_volterra_denominator_of_root
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T14:15:08.613203+00:00
-- url     : https://prove2.me/theorems/41fec73f-7e42-4e71-8db4-3aa9a8d1fb2e
-- title:
--   Gaussian Esscher-root Volterra denominator for the native Lévy exponent
-- statement:
--   For the original spectrally negative Lévy process, the q-shifted exponent at an Esscher root equals a corrected linear drift, the Gaussian quadratic term, and the real exponential jump compensator. The correction for jumps of magnitude exactly one is retained. This connects the generic Volterra exponent identity to the exact process exponent used in scale-function Laplace inversion.
-- source:
--   Derived from the published and proved gaussian_laplaceExponent_esscher_shift_unit_atom by unfolding SpectrallyNegativeLevy.ψ and using the root equation.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_gaussian_laplaceExponent_esscher_shift_unit_atom
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.gaussian_esscher_psi_volterra_denominator_of_root
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ θ : ℝ) (hφ : 0 < φ) (hθ : 0 ≤ θ) (hroot : X.ψ φ = q)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂(X.ν.map (fun y : ℝ => -y))) < ⊤) :
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
