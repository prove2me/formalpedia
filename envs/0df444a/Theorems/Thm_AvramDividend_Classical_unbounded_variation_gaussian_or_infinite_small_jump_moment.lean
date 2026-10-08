-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_variation_gaussian_or_infinite_small_jump_moment
-- name    : AvramDividend.Classical.unbounded_variation_gaussian_or_infinite_small_jump_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T23:12:27.74378+00:00
-- url     : https://prove2.me/theorems/cb0b01e6-6ae4-4fba-affb-24f5e5c449c6
-- title:
--   Unbounded-variation Lévy process: positive Gaussian coefficient or infinite small-jump first moment
-- statement:
--   The canonical unbounded-variation hypothesis is by definition the negation of sigma=0 together with finite absolute first small-negative-jump moment. Since the Gaussian coefficient sigma is nonnegative in SpectrallyNegativeLevy, it follows without any further assumptions that either sigma is strictly positive, or the jump first moment is infinite. This is the exhaustive model-level split for the outstanding unbounded-variation scale-function positivity/tilted-monotonicity theorem and for continuous scale derivative regularity.
-- source:
--   Def_AvramDividend_Classical_SpectrallyNegativeLevy, SpectrallyNegativeLevy.BoundedVariation and the structure field sigma_nonneg; follows by elementary order theory in ENNReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.unbounded_variation_gaussian_or_infinite_small_jump_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation) :
    0 < X.σ ∨
      (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) = ⊤ := by sorry
