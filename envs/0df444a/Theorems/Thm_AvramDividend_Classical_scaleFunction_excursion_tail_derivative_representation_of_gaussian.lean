-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_excursion_tail_derivative_representation_of_gaussian
-- name    : AvramDividend.Classical.scaleFunction_excursion_tail_derivative_representation_of_gaussian
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T22:02:35.181238+00:00
-- url     : https://prove2.me/theorems/28594252-e53f-4e75-aed4-02ee12d04ec5
-- title:
--   Esscher excursion-tail derivative factorisation with positive Gaussian coefficient
-- statement:
--   For a standing spectrally negative Lévy process with a nonzero Gaussian component, construct the positive Esscher root and its descending-excursion height measure. Show finite positive upper tails and absence of height atoms, then establish differentiability of the q-scale function and its logarithmic derivative representation. This is the Gaussian-specific fluctuation-theory input, rather than a calculus shortcut.
-- source:
--   Chan, Kyprianou and Savov (2011), Smoothness of scale functions for spectrally negative Lévy processes, excursion-height differentiability and atomlessness criterion; Kuznetsov, Kyprianou and Rivero (2012), positive Esscher root and fluctuation identities.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_excursion_tail_derivative_representation_of_gaussian
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
        {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
        (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
        (q : ℝ) (hq : 0 < q)
        (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) :
    ∃ (φ : ℝ) (μ : Measure ℝ),
      0 < φ ∧ NullSingletonClass μ ∧
      (∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x) ∧
      (∀ x : ℝ, 0 < x →
        deriv W x = W x * (φ + μ.real (Ici x))) := by sorry
