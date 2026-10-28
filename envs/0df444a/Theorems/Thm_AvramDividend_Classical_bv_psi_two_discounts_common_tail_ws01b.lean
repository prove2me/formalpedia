-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_psi_two_discounts_common_tail_ws01b
-- name    : AvramDividend.Classical.bv_psi_two_discounts_common_tail_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T13:12:51.739992+00:00
-- url     : https://prove2.me/theorems/4cd6f916-0c5b-459d-a961-9dc328d293e5
-- title:
--   Common Laplace-exponent tail for two discounts under standing bounded variation
-- statement:
--   For a spectrally negative bounded-variation Lévy process satisfying the Standing conditions, prove its positive drift and zero-normalised exponent deficit imply that the exponent exceeds any two nonnegative discount rates on a common positive right tail. This supplies the precise Laplace integrability premise of the already proved generic two-scale-function resolvent-convolution identity, enabling the BV analytic killed-resolvent branch.
-- source:
--   Kuznetsov, Kyprianou and Rivero, The Theory of Scale Functions for Spectrally Negative Lévy Processes; accepted Prove2Me BV exponent asymptotic fc81170b and standing positive drift f5ce6b06.

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_bv_exponent_gap_div_tendsto_zero
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Order.Filter.Tendsto

open AvramDividend.Classical MeasureTheory Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_psi_two_discounts_common_tail_ws01b
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ θ : ℝ, b < θ →
      0 ≤ θ ∧ q₁ < X.ψ θ ∧ q₂ < X.ψ θ := by sorry
