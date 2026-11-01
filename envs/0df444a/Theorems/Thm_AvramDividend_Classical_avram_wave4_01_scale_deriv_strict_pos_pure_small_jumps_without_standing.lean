-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_scale_deriv_strict_pos_pure_small_jumps_without_standing
-- name    : AvramDividend.Classical.avram_wave4_01_scale_deriv_strict_pos_pure_small_jumps_without_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:24:22.074644+00:00
-- url     : https://prove2.me/theorems/04f0dc06-50ba-4cd1-8936-7272afaf6545
-- title:
--   Strictly positive ordinary q-scale derivative from genuine original first-record discount, without Standing
-- statement:
--   For every positive discount q and every spectrally negative Lévy process with divergent first small-negative-jump absolute moment, the ordinary derivative of the q-scale function is strictly positive at every positive reserve. The source first-record hazard is bounded below by the strictly positive unrestricted Laplace root, and W(a)>0; neither a Standing assumption nor excursion differentiability is needed.
-- source:
--   Proved positive Esscher root cfe6d3e1, infinite-small-jump implies unbounded variation, positive W e50526dc and original-process hazard lower bound (new Wave4 Chat01).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_log_slope_ge_positive_esscher_root

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_01_scale_deriv_strict_pos_pure_small_jumps_without_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤) :
    ∀ a : ℝ, 0 < a → 0 < deriv W a := by sorry
