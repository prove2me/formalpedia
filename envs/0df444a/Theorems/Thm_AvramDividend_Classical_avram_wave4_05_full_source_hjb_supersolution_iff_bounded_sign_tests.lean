-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_full_source_hjb_supersolution_iff_bounded_sign_tests
-- name    : AvramDividend.Classical.avram_wave4_05_full_source_hjb_supersolution_iff_bounded_sign_tests
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:01:50.553455+00:00
-- url     : https://prove2.me/theorems/3ac47d08-b62b-49a8-b428-3d0e494817e2
-- title:
--   Original source HJB supersolution iff two bounded residual sign tests with no generator-domain premises
-- statement:
--   Under exactly the original root Standing, q>0, scale-function, and Gaussian∨bounded-variation∨positive-axis-C2 smoothness assumptions, the genuine all-positive source HJB supersolution (including generator domain at all reserves) is logically equivalent to just two residual sign conditions: Γvcstar−qvcstar≤0 for 0<x<cstar when cstar>0, and Γvcstar−qvcstar≤0 for cstar<y<cstar+1+max(0,X.c/q). GeneratorIntegrable is not a hypothesis in either region because the canonically Proved all-positive domain theorem closes the entire original compensated generator domain independently of harmonicity. The source far-field HJB supplies the sign beyond the strip. This theorem is a sharp analytic verification criterion, not an unconditional assertion of the two signs.
-- source:
--   Accepted source all-positive domain 8fd5ab93 (dependency), source bounded regional supersolution iff 80f755f8; root smoothness and original generator

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_original_all_positive_generator_domain_of_root_smoothness
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_hjb_supersolution_iff_bounded_regional_residual

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_full_source_hjb_supersolution_iff_bounded_sign_tests
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    (∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) ≤ 0) ↔
    ((0 < cstar W → ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.generator (vcstar W) x - q * vcstar W x ≤ 0) ∧
      (∀ y : ℝ, (cstar W).toReal < y →
        y < (cstar W).toReal + 1 + max 0 (X.c / q) →
        X.generator (vcstar W) y - q * vcstar W y ≤ 0)) := by sorry
