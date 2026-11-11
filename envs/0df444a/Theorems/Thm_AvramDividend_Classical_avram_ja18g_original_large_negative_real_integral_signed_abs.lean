-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_large_negative_real_integral_signed_abs
-- name    : AvramDividend.Classical.avram_ja18g_original_large_negative_real_integral_signed_abs
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T02:58:56.726627+00:00
-- url     : https://prove2.me/theorems/670b0a99-21d6-4867-b267-ad5b1991d3a7
-- title:
--   Original Lévy negative-large signed integral equals minus absolute lintegral
-- statement:
--   With the original negative-large-mark first moment finite under Standing, integrate the pointwise identity z=-|z| on Iic(-1) and convert its real Bochner integral into minus the ENNReal absolute lintegral. This is a straightforward signed-to-ENNReal measure-theory lemma.
-- source:
--   J-A18 signed Campbell mean bridge

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18g_original_large_negative_real_integral_signed_abs
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    (∫ z in Iic (-1 : ℝ), z ∂X.ν) =
      - (∫⁻ z in Iic (-1 : ℝ), ENNReal.ofReal |z| ∂X.ν).toReal := by sorry
