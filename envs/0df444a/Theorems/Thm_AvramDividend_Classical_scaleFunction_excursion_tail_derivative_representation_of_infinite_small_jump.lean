-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_excursion_tail_derivative_representation_of_infinite_small_jump
-- name    : AvramDividend.Classical.scaleFunction_excursion_tail_derivative_representation_of_infinite_small_jump
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T22:03:06.32287+00:00
-- url     : https://prove2.me/theorems/55c2640d-d105-413d-88bc-254061aa5139
-- title:
--   Esscher excursion-tail derivative factorisation with infinite small-jump first moment
-- statement:
--   For a standing spectrally negative Lévy process whose small negative jumps have infinite absolute first moment, construct the Esscher root and descending-excursion height measure. Prove its positive tail masses are finite and atomless, then derive W'(x)=W(x)(Phi(q)+mu([x,infinity))) on positive x. This is the infinite-activity/unbounded-variation fluctuation-theory input, not an assumption of C1 or a restatement of the canonical disjunction.
-- source:
--   Chan, Kyprianou and Savov (2011), Smoothness of scale functions for spectrally negative Lévy processes, excursion-height differentiability and atomlessness criterion; Kuznetsov, Kyprianou and Rivero (2012), positive Esscher root and fluctuation identities.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_excursion_tail_derivative_representation_of_infinite_small_jump
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
        {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
        (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
        (q : ℝ) (hq : 0 < q)
        (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) = ⊤) :
    ∃ (φ : ℝ) (μ : Measure ℝ),
      0 < φ ∧ NullSingletonClass μ ∧
      (∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x) ∧
      (∀ x : ℝ, 0 < x →
        deriv W x = W x * (φ + μ.real (Ici x))) := by sorry
