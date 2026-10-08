-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_excursion_tail_derivative_representation_of_bv_ac
-- name    : AvramDividend.Classical.scaleFunction_excursion_tail_derivative_representation_of_bv_ac
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T15:06:30.946108+00:00
-- url     : https://prove2.me/theorems/7b6ee66e-778a-4d71-8c26-6031df4c0a7a
-- title:
--   Excursion-tail derivative representation in the bounded-variation absolutely-continuous case
-- statement:
--   For a standing bounded-variation spectrally negative Lévy process whose Lévy measure is absolutely continuous, choose the positive Esscher root Phi(q). Absolute continuity removes atoms in the excursion-height law, giving finite atomless positive tails and differentiability of the q-scale function, with W'(x)=W(x)(Phi(q)+mu([x,infinity))).
-- source:
--   Chan, Kyprianou and Savov (2011), bounded-variation smoothness criterion via atomlessness; Kuznetsov, Kyprianou and Rivero (2012), Esscher identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_excursion_tail_derivative_representation_of_bv_ac
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (hac : X.ν ≪ volume) :
    ∃ (φ : ℝ) (μ : Measure ℝ),
      0 < φ ∧ NullSingletonClass μ ∧
      (∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x) ∧
      (∀ x : ℝ, 0 < x → deriv W x = W x * (φ + μ.real (Ici x))) := by sorry
