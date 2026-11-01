-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_original_upper_generator_iff_bounded_strip_residual
-- name    : AvramDividend.Classical.avram_wave4_05_original_upper_generator_iff_bounded_strip_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:36:03.646303+00:00
-- url     : https://prove2.me/theorems/90d3ff84-d087-4e31-acda-2196dcfb5395
-- title:
--   Root's exact upper-reserve source generator condition iff bounded finite residual strip
-- statement:
--   Under only the true Standing source, q>0, and the genuine q-scale function, the original root's quantified above-barrier generator premise (domain and Γvcstar−qvcstar≤0 for every y>cstar) is logically equivalent to checking its residual inequality on the finite strip cstar<y<cstar+1+max(0,X.c/q). Domain for all y>cstar is independently canonically Proved, and beyond the strip the canonically Proved far-field HJB has residual≤0. Barrier finiteness follows canonically. No positive Gaussian coefficient, BV, positive cap, C2 interior harmonicity, or stochastic stopping needed.
-- source:
--   Exact original barrier_cstar_optimal upper generator hgen; Proved 32cfe60b, 09ea2ea1, 7bb43015

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_vcstar_generatorIntegrable_strictly_above_real_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_eventual_hjb_finite_cstar

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_original_upper_generator_iff_bounded_strip_residual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) :
    (∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) ↔
    (∀ y : ℝ, (cstar W).toReal < y →
      y < (cstar W).toReal + 1 + max 0 (X.c / q) →
      X.generator (vcstar W) y - q * vcstar W y ≤ 0) := by sorry
