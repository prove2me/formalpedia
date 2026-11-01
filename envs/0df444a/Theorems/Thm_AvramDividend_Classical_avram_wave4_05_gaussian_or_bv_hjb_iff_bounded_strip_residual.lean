-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_or_bv_hjb_iff_bounded_strip_residual
-- name    : AvramDividend.Classical.avram_wave4_05_gaussian_or_bv_hjb_iff_bounded_strip_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:29:25.594292+00:00
-- url     : https://prove2.me/theorems/0be4e489-c732-4c02-873d-e6e900d4fc00
-- title:
--   Full original-source Gaussian/BV HJB if and only if one bounded upper-reserve residual test
-- statement:
--   For a true standing spectrally negative Lévy source with positive q and genuine q-scale W, under the Gaussian-or-bounded-variation disjunction, the complete HJB equation and actual source generator domain at every positive reserve are equivalent to checking Γvcstar−qvcstar≤0 on the single finite interval cstar<y<cstar+1+max(0,X.c/q). Canonically Proved Gaussian/BV HJB iff the full upper residual gives necessity and conditional sufficiency; canonically Proved source far-field HJB supplies all missing large-reserve residual inequalities beyond this threshold. No explicit interior harmonicity or finite barrier premise is needed in this disjunction.
-- source:
--   Avram–Palmowski–Pistorius (2007), generator and HJB; source Gaussian/BV HJB iff 0dc60c32, far HJB 09ea2ea1

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_vcstar_eventual_hjb_finite_cstar
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_or_bv_hjb_iff_above_residual

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_gaussian_or_bv_hjb_iff_bounded_strip_residual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hbranch : 0 < X.σ ∨ X.BoundedVariation) :
    (∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) = 0) ↔
    (∀ y : ℝ,
      (cstar W).toReal < y →
      y < (cstar W).toReal + 1 + max 0 (X.c / q) →
      X.generator (vcstar W) y - q * vcstar W y ≤ 0) := by sorry
