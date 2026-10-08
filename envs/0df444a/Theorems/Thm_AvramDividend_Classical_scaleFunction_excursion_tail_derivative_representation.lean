-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_excursion_tail_derivative_representation
-- name    : AvramDividend.Classical.scaleFunction_excursion_tail_derivative_representation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T14:55:41.265408+00:00
-- url     : https://prove2.me/theorems/1ef87426-41aa-4ae4-93a5-fef30bdd050b
-- title:
--   q-scale derivative as Esscher root plus atomless excursion-height tail
-- statement:
--   For q>0 under the standing condition (3.3), choose the positive Esscher root phi=Phi(q). Under the phi-Esscher transform, the q-scale function is exp(phi x) times a zero-scale function. There is a descending-excursion height measure mu whose upper tails are finite above every positive height and have no atoms under condition (3.3). The scale function is differentiable on (0,infinity), and its logarithmic derivative is phi plus the excursion-height tail: W'(x)=W(x)(phi+mu([x,infinity))). This is the precise stochastic smoothness input needed for derivative continuity; all later continuity reasoning is deterministic.
-- source:
--   Chan, Kyprianou and Savov (2011), Smoothness of scale functions for spectrally negative Levy processes, one-sided derivative/excursion-height identities and atomlessness criterion; Kuznetsov, Kyprianou and Rivero (2012), Esscher identity W^(q)(x)=exp(Phi(q)x) W_Phi(q)(x).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_excursion_tail_derivative_representation
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ (φ : ℝ) (μ : Measure ℝ),
      0 < φ ∧
      NullSingletonClass μ ∧
      (∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x) ∧
      (∀ x : ℝ, 0 < x →
        deriv W x = W x * (φ + μ.real (Ici x))) := by sorry
