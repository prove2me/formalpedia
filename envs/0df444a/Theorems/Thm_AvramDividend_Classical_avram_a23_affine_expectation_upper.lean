-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a23_affine_expectation_upper
-- name    : AvramDividend.Classical.avram_a23_affine_expectation_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:54:02.314032+00:00
-- url     : https://prove2.me/theorems/95598427-77e6-405c-964a-0fc833a2e58c
-- title:
--   Probabilistic affine spatial mesh bound transfers pointwise to L1 expectation
-- statement:
--   On the actual original probability law, an integrable a.e pointwise bound f≤ε+L g transfers to the expected bound E f≤ε+L E g, by integral monotonicity, linearity and probability normalisation. This is used with HJB value spatial error f and true Gaussian reserve gap g.
-- source:
--   Elementary affine expectation bound for true Gaussian spatial L1 mesh errors.

import Mathlib
open MeasureTheory

theorem AvramDividend.Classical.avram_a23_affine_expectation_upper
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (f g : Ω → ℝ) (hf : Integrable f P) (hg : Integrable g P)
    (ε L : ℝ)
    (hpoint : ∀ᵐ ω ∂P, f ω ≤ ε + L * g ω) :
    (∫ ω, f ω ∂P) ≤ ε + L * (∫ ω, g ω ∂P) := by sorry
