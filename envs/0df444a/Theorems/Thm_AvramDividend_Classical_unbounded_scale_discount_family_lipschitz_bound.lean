-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_family_lipschitz_bound
-- name    : AvramDividend.Classical.unbounded_scale_discount_family_lipschitz_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:16:08.05307+00:00
-- url     : https://prove2.me/theorems/7d44b824-2996-4902-a2fd-0896ff50cbe7
-- title:
--   Uniform Lipschitz bound of q-scale functions on compact discount intervals
-- statement:
--   Let W_q be any scale-function family for an unbounded-variation spectrally negative Lévy process, indexed by all nonnegative discounts up to Q. For every fixed positive reserve, its dependence on q satisfies a two-sided global Lipschitz bound on [0,Q], with constant given by the Q-scale self-convolution. In particular the family is continuous with respect to discount.
-- source:
--   A two-sided orientation of the proved uniform q-discount secant bound.

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_uniform_secant_bound
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_discount_family_lipschitz_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (W : ℝ → ℝ → ℝ)
    (hW : ∀ q ∈ Icc (0 : ℝ) Q, IsScaleFunction X q (W q))
    (x : ℝ) (hx : 0 < x) :
    ∀ a ∈ Icc (0 : ℝ) Q, ∀ b ∈ Icc (0 : ℝ) Q,
      |W b x - W a x| ≤ |b - a| *
        ∫ s in Ioc (0 : ℝ) x, W Q s * W Q (x - s) := by sorry
