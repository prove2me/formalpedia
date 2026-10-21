-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_esscher_excursion_integrated_scale_representation
-- name    : AvramDividend.Classical.unbounded_esscher_excursion_integrated_scale_representation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-20T19:23:37.89699+00:00
-- url     : https://prove2.me/theorems/49acdc06-9a71-482c-b742-ff432e034677
-- title:
--   Esscher excursion measure and integrated scale-function representation for the unbounded-variation case, without standing assumptions
-- statement:
--   When the spectrally negative Levy process has unbounded variation, the q-scale function is still C1 on the positive half-line. The proof needs an excursion-height intensity for the Esscher-tilted process, and the standing assumptions must not be required: the only structural hypothesis is that the process is not of bounded variation. Concretely, one needs a positive Esscher root phi with psi(phi) = q, and an atomless excursion-height intensity measure mu whose positive tails are finite, such that the q-scale function satisfies the integrated exponential representation W b = W a * exp(integral from a to b of phi + mu.real (Ici t)) for all 0 < a <= b. This isolates the probabilistic core that the C1 conclusion needs: constructing the tilted excursion intensity, proving its tails are finite and continuous, and establishing the excursion no-crossing identity. Differentiating the interval identity is a separate, already proved analytic theorem. The standing assumptions are deliberately absent: the integrable first moment of the positive part is not available when the Levy measure has infinite first moment near zero, and the infinite-small-jump case is exactly the regime this theorem must cover.
-- source:
--   Chan, Kyprianou, Savov (2011), Smoothness of scale functions for spectrally negative Levy processes, equations (3)-(6); Kuznetsov, Kyprianou, Rivero (2012), The Theory of Scale Functions for Spectrally Negative Levy Processes, Lemma 2.4 and sections 2.17-2.19; Kyprianou (2011), Excursions and Stochasticity, lecture notes on the excursion-height intensity and the Esscher transform.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_esscher_excursion_integrated_scale_representation
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    ∃ (φ : ℝ) (μ : Measure ℝ),
      0 < φ ∧ NullSingletonClass μ ∧
      (∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) ∧
      ContinuousOn (fun t : ℝ => μ.real (Ici t)) (Ioi 0) ∧
      (∀ a b : ℝ, 0 < a → a ≤ b →
        W b = W a * Real.exp (∫ t in a..b, φ + μ.real (Ici t))) := by sorry
