-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_excursion_tail_derivative_representation_of_unbounded
-- name    : AvramDividend.Classical.scaleFunction_excursion_tail_derivative_representation_of_unbounded
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T15:06:15.762552+00:00
-- url     : https://prove2.me/theorems/f5af64fd-b5e8-4286-b033-29b2b8b5eda6
-- title:
--   Excursion-tail derivative representation in the unbounded-variation case
-- statement:
--   For a standing unbounded-variation spectrally negative Lévy process and q>0, choose the positive Esscher root Phi(q). Under the Esscher transform the zero-scale excursion-height measure has finite tails above each positive level and no atoms, and the q-scale derivative satisfies W'(x)=W(x)(Phi(q)+mu([x,infinity))). This combines the standard one-sided excursion derivative identities with the fact that unbounded variation gives differentiability on the positive half-line.
-- source:
--   Chan, Kyprianou and Savov (2011), Smoothness of scale functions; Kuznetsov, Kyprianou and Rivero (2012), Esscher transform and scale-function identities.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_excursion_tail_derivative_representation_of_unbounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : ¬ X.BoundedVariation) :
    ∃ (φ : ℝ) (μ : Measure ℝ),
      0 < φ ∧ NullSingletonClass μ ∧
      (∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x) ∧
      (∀ x : ℝ, 0 < x → deriv W x = W x * (φ + μ.real (Ici x))) := by sorry
