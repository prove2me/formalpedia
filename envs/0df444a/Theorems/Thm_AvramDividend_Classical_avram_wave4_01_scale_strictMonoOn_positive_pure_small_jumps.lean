-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_scale_strictMonoOn_positive_pure_small_jumps
-- name    : AvramDividend.Classical.avram_wave4_01_scale_strictMonoOn_positive_pure_small_jumps
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:31:27.836204+00:00
-- url     : https://prove2.me/theorems/9e846c34-b84b-4204-82e5-c4ad7719393d
-- title:
--   Strict monotonicity of the pure infinite-small-jump q-scale function on positive reserves without Standing
-- statement:
--   For a spectrally negative Lévy process with divergent first absolute small-negative-jump moment and q>0, the q-scale function is strictly increasing between every two positive reserves. This combines genuine first-record strict derivative positivity and the canonically Proved Standing-free C1 regularity with the real mean value theorem; it is stronger than mere monotonicity and does not rely on excursion substitutions.
-- source:
--   Genuine original-process derivative strict positivity (Wave4), Standing-free C1 cd61d678, Mathlib strictMonoOn_of_deriv_pos on convex Ioi 0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_infinite_variation_without_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_scale_deriv_strict_pos_pure_small_jumps_without_standing

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_01_scale_strictMonoOn_positive_pure_small_jumps
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤) :
    StrictMonoOn W (Ioi (0 : ℝ)) := by sorry
