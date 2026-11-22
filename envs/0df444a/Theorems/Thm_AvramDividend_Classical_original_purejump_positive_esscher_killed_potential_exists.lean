-- Prove2me | Theorems.Thm_AvramDividend_Classical_original_purejump_positive_esscher_killed_potential_exists
-- name    : AvramDividend.Classical.original_purejump_positive_esscher_killed_potential_exists
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T15:32:08.134478+00:00
-- url     : https://prove2.me/theorems/60cac980-885d-4ed8-a9fb-a3e0b5d76828
-- title:
--   Original purejump UBV finite atomless killed ladder potential at positive Esscher base
-- statement:
--   For the original standing pure-jump spectrally negative Lévy process with unbounded variation, fix any positive Esscher base φ with ψ(φ)>0. There exists an atomless finite measure U on positive heights with mass φ/ψ(φ) and Laplace transform (φ+s)/ψ(φ+s) for every s>0. This U is the killed descending ladder renewal potential at the positive base. It arises from the genuine original Lévy-tail kernel κφ(t)=e^(−φt)ν((−∞,−t)), the proved killed Bernstein identity, finite geometric approximants, tight weak limits, and the Laplace-derivative/convolution proof of atomlessness. It is significantly narrower than zero-discount scale existence because it fixes one strictly killed positive Esscher parameter, and its finite mass permits probability methods.
-- source:
--   Proved original killed Bernstein 0cb20c38, source lower bound fd68d5d9, kernel AC 501256a2, finite geometric potential 9f7bf7a2, tightness f2895e24, Laplace limit 32aa3f05, atomless weighted measure 40d18dd0, original UBV tail divergence 8f9e6281, atomzero 9f464a39.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.original_purejump_positive_esscher_killed_potential_exists
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hσ : X.σ = 0)
    (φ : ℝ) (hφ : 0 < φ) (hψ : 0 < X.ψ φ) :
    ∃ U : Measure ℝ,
      U (Iic (0 : ℝ)) = 0 ∧
      (∀ x : ℝ, U {x} = 0) ∧
      U Set.univ = ENNReal.ofReal (φ / X.ψ φ) ∧
      (∀ s : ℝ, 0 < s →
        IntegrableOn (fun y : ℝ => Real.exp (-(s * y))) (Ioi 0) U ∧
        ∫ y in Ioi (0 : ℝ),
          Real.exp (-(s * y)) ∂U =
            (φ + s) / X.ψ (φ + s)) := by sorry
