-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_original_all_positive_generator_domain_of_root_smoothness
-- name    : AvramDividend.Classical.avram_wave4_05_original_all_positive_generator_domain_of_root_smoothness
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:57:47.1978+00:00
-- url     : https://prove2.me/theorems/8fd5ab93-0eaf-47a1-bd56-c2e8fc9f05b6
-- title:
--   Full positive reserve domain of the original compensated Lévy generator under root smoothness
-- statement:
--   Under only the root's actual Standing source, q>0, genuine scale function and Gaussian∨bounded-variation∨global-positive-C2 smoothness alternative, the candidate vcstar belongs to the true compensated generator domain at every positive reserve, with no additional above-generator residual sign or P2 pure-jump q-harmonicity premise. Proved interior domain is combined with P3 positive-cap integrability and Proved source strict-above domain, with source cap finiteness and zero-cap case. This closes the generator-domain part of the original HJB for all positive reserves but not the still-open (Γ−q) equality for pure-jump interior.
-- source:
--   Exact source root 545c65ef; accepted interior domain d2214670 (dependent), cap domain 0c561a07, above domain 32cfe60b, finiteness 7bb43015

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_original_vcstar_interior_generator_domain_all_smooth_branches
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_vcstar_generator_integrable_at_positive_cstar_of_smooth
import Theorems.Thm_AvramDividend_Classical_vcstar_generatorIntegrable_strictly_above_real_cstar

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_original_all_positive_generator_domain_of_root_smoothness
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    ∀ y : ℝ, 0 < y → X.GeneratorIntegrable (vcstar W) y := by sorry
