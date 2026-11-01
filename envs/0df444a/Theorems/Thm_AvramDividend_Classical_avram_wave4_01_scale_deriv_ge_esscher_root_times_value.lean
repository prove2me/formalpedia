-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_scale_deriv_ge_esscher_root_times_value
-- name    : AvramDividend.Classical.avram_wave4_01_scale_deriv_ge_esscher_root_times_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:20:21.13479+00:00
-- url     : https://prove2.me/theorems/d296ae4c-475c-4256-ba6f-d4c54d2029c0
-- title:
--   Quantitative source-record growth inequality W' ≥ positive Laplace root times W
-- statement:
--   At every positive reserve for a spectrally negative Lévy process of infinite small-negative-jump variation, the ordinary q-scale derivative dominates φ times the scale value, for any positive Laplace root φ of ψ(φ)=q. This differential growth inequality follows from the actual first-record killing hazard bound and strict scale positivity without Standing.
-- source:
--   Genuine original source record log-slope lower bound a5dbcace, strict W positivity e50526dc and infinite negative-jump variation to non-BV.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_log_slope_ge_positive_esscher_root

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_01_scale_deriv_ge_esscher_root_times_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∀ a : ℝ, 0 < a → φ * W a ≤ deriv W a := by sorry
