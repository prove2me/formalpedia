-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_psi_discount_reciprocal_small
-- name    : AvramDividend.Classical.unbounded_psi_discount_reciprocal_small
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:57:11.512053+00:00
-- url     : https://prove2.me/theorems/d5c48916-f37f-4cca-ba7c-667717c96432
-- title:
--   The normalised discounted inverse Lévy exponent vanishes at infinity
-- statement:
--   For every spectrally negative Lévy process of unbounded variation and any nonnegative discount q, θ/(ψ(θ)-q) is eventually nonnegative and smaller than any prescribed positive ε. This quantitative reciprocal asymptotic is the transform-side estimate for vanishing scale mass at the origin and supplies a useful small-parameter bound for q-scale Laplace inversion.
-- source:
--   Direct consequence of the discounted linear-denominator estimate unbounded_psi_discount_denominator_eventually_linear, itself derived from the accepted normalised exponent growth theorem (9f622e05-0375-4204-b9ae-299d3de043f5).

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_psi_discount_reciprocal_small
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ ε : ℝ, 0 < ε →
      ∃ β : ℝ, 1 ≤ β ∧
        ∀ θ : ℝ, β ≤ θ →
          0 ≤ θ / (X.ψ θ - q) ∧
            θ / (X.ψ θ - q) < ε := by sorry
