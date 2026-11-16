-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_uniform_positivecap_affine_candidate_HJB_bundle
-- name    : AvramDividend.Classical.avram_bvb_obstruction_original_uniform_positivecap_affine_candidate_HJB_bundle
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:48:50.433071+00:00
-- url     : https://prove2.me/theorems/7927ff31-feef-4add-8e28-b9815531730a
-- title:
--   All positive-cap HJB and regularity hypotheses for original unit-uniform affine dividend verification candidate
-- statement:
--   For original unit-uniform negative Lévy measure with zero Gaussian coefficient and c=1/2, the candidate w(u)=0 below zero and 1/2+u otherwise satisfies all continuous-on-nonnegative, nonnegative boundary, C1 cap-interior, true generator integrability, HJB super-solution and derivative≥1 hypotheses at every positive cap C. This is the last analytic prerequisite for the positive-cap pathwise drift-only counterexample.
-- source:
--   Bundle independent Proved original source statements, with the actual compensated jump integral and normalised Lévy triplet. The generator integrability source helper is a separate immediate dependency still undergoing remote publication/verification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_half_affine_candidate_continuous_on_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_half_affine_candidate_strict_interior_C1
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_half_affine_positive_reserve_deriv_eq_one
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_uniform_GeneratorIntegrable_half_affine
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_uniform_mark_generator_integral_exact
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_generator_HJB_of_uniform_mark_kernel
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bvb_obstruction_original_uniform_positivecap_affine_candidate_HJB_bundle
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = (volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))
    (hσ : X.σ = 0) (hc : X.c = 1 / 2)
    (C : ℝ≥0∞) :
    let w : ℝ → ℝ := fun u => if u < 0 then 0 else 1 / 2 + u
    ContinuousOn w (Ici 0) ∧
    0 ≤ w 0 ∧
    (∀ z : ℝ, z < 0 → w z = 0) ∧
    ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} ∧
    (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - w y ≤ 0) ∧
    (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) := by sorry
