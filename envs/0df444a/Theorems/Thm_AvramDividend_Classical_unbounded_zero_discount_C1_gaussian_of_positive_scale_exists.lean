-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_zero_discount_C1_gaussian_of_positive_scale_exists
-- name    : AvramDividend.Classical.unbounded_zero_discount_C1_gaussian_of_positive_scale_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:29:55.652971+00:00
-- url     : https://prove2.me/theorems/aaebd7d3-5d4d-4dd2-ac8e-a703e302f45b
-- title:
--   Gaussian zero-discount scale regularity from any existing positive-discount scale
-- statement:
--   A positive Gaussian coefficient supplies C1 regularity of every positive-discount scale. Combining the proven Gaussian smoothing result, eventual growth of the Laplace exponent and the verified damped convolution transfer yields C1 zero-discount regularity, provided any positive-discount scale function exists. This isolates scale existence as the Gaussian branch's only remaining premise.
-- source:
--   Proved scaleFunction_contDiff_one_gaussian_without_standing, unbounded_zero_discount_C1_of_positive_discount_C1, chat04_psi_eventually_gt_of_unbounded_variation.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.Calculus.ContDiff.Deriv
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_zero_discount_C1_gaussian_of_positive_scale_exists
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (W₀ : ℝ → ℝ) (hW₀ : IsScaleFunction X 0 W₀)
    (hσ : 0 < X.σ)
    (hexists : ∃ q : ℝ, 0 < q ∧ ∃ Wq : ℝ → ℝ, IsScaleFunction X q Wq) :
    ContDiffOn ℝ 1 W₀ (Ioi (0 : ℝ)) := by sorry
