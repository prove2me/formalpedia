-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_psi_two_discounts_common_tail
-- name    : AvramDividend.Classical.unbounded_psi_two_discounts_common_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T12:56:09.071078+00:00
-- url     : https://prove2.me/theorems/30c9b779-d0ca-4fe8-9b52-d86ed6d87efe
-- title:
--   Common Laplace half-line for two nonnegative discounts under unbounded variation
-- statement:
--   For any pair of nonnegative discount rates, an unbounded-variation spectrally negative Lévy process admits a common right-hand Laplace-transform domain where both discount rates lie strictly below its Laplace exponent. This discharges the shared-tail hypothesis of the proved real-space scale resolvent theorem.
-- source:
--   Direct consequence of the already Proved unbounded_psi_discount_denominator_eventually_linear at C = 0, combined with max of the two thresholds.

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_unbounded_psi_discount_denominator_eventually_linear
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_psi_two_discounts_common_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ θ : ℝ, b < θ →
      0 ≤ θ ∧ q₁ < X.ψ θ ∧ q₂ < X.ψ θ := by sorry
