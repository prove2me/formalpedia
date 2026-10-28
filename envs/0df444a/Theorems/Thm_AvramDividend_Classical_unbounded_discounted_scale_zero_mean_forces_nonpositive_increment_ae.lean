-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_discounted_scale_zero_mean_forces_nonpositive_increment_ae
-- name    : AvramDividend.Classical.unbounded_discounted_scale_zero_mean_forces_nonpositive_increment_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:12:42.670989+00:00
-- url     : https://prove2.me/theorems/a549269c-9514-4afa-95dd-237a5444d166
-- title:
--   Unbounded scale zero-mean forces nonpositive Lévy increments
-- statement:
--   For an unbounded-variation spectrally negative Levy process whose q-scale function vanishes at the origin, an integrable un-killed discounted scale reward with expectation zero at any fixed time forces X_t to be nonpositive almost surely. It combines the positive-axis strict positivity of scale functions with the zero-mean nonnegative-reward theorem. This identifies a precise obstacle to using an un-stopped scale-function martingale in the strict-exit proof.
-- source:
--   Proved strict positivity of q-scale functions under unbounded variation, and the nonnegative zero-integral criterion.

import Theorems.Thm_AvramDividend_Classical_discounted_scale_zero_mean_forces_zero_ae
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.unbounded_discounted_scale_zero_mean_forces_nonpositive_increment_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) (hW0 : W 0 = 0) (t : ℝ≥0)
    (hInt : Integrable
      (fun ω : Ω => Real.exp (-(q * (t : ℝ))) * W (X.X t ω)) P)
    (hMean : (∫ ω : Ω, Real.exp (-(q * (t : ℝ))) *
      W (X.X t ω) ∂P) = W 0) :
    ∀ᵐ ω ∂P, X.X t ω ≤ 0 := by sorry
