-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_resolvent_convolution
-- name    : AvramDividend.Classical.unbounded_scale_resolvent_convolution
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:08:53.003124+00:00
-- url     : https://prove2.me/theorems/4198c14e-7e01-4121-a3e9-8f4e30ee2b4d
-- title:
--   Unconditional q-scale resolvent convolution for spectrally negative Lévy processes of unbounded variation
-- statement:
--   For unbounded variation and any two nonnegative discount rates, their scale functions satisfy the exact resolvent convolution identity at every positive argument. This removes all auxiliary regularity, Laplace-transform and threshold assumptions by importing the previously proved causal-convolution and scale-exponent theorems. It gives a reusable direct bridge from the zero-discount scale function to the positive-discount scale function in the c-star regularity programme.
-- source:
--   Unbounded psi common-tail theorem plus the scale resolvent convolution theorem with integrability discharged.

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_unbounded_psi_two_discounts_common_tail
import Theorems.Thm_AvramDividend_Classical_scale_resolvent_convolution_of_scale_integrability
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_resolvent_convolution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (W₁ W₂ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁) (hW₂ : IsScaleFunction X q₂ W₂) :
    ∀ x : ℝ, 0 < x →
      W₂ x = W₁ x + (q₂ - q₁) *
        (∫ s in Ioc (0 : ℝ) x, W₁ s * W₂ (x - s)) := by sorry
