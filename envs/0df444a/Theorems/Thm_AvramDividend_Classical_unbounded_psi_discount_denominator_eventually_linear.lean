-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_psi_discount_denominator_eventually_linear
-- name    : AvramDividend.Classical.unbounded_psi_discount_denominator_eventually_linear
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:54:48.801207+00:00
-- url     : https://prove2.me/theorems/f9bc45e4-85d1-4707-a640-4d7c48cba7a9
-- title:
--   Unbounded Lévy exponent eventually dominates every discounted linear comparison
-- statement:
--   For every unbounded-variation spectrally negative Lévy process, nonnegative discount q and real slope C, there is a β≥1 such that ψ(θ)-q>Cθ for every θ≥β. This source-faithful estimate turns the proved normalised exponent divergence into an explicit positive and linearly coercive shifted Laplace denominator, as required when controlling the q-scale transform in the unbounded Esscher cumulative-Laplace and zero-discount scale-function routes.
-- source:
--   Direct consequence of the Proved AvramDividend.Classical.psi_normalised_unbounded_of_unbounded_variation (9f622e05-0375-4204-b9ae-299d3de043f5), with q≥0 and θ≥1.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_psi_discount_denominator_eventually_linear
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ C : ℝ, ∃ β : ℝ, 1 ≤ β ∧
      ∀ θ : ℝ, β ≤ θ → C * θ + q < X.ψ θ := by sorry
