-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_automatic_ruin_crossing_tail_finite
-- name    : AvramDividend.Classical.avram_mix_inf20_original_finitecap_automatic_ruin_crossing_tail_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:23:47.499961+00:00
-- url     : https://prove2.me/theorems/79dafd17-55b5-4413-8220-d47330546ae5
-- title:
--   Original positive finite cap automatically separates all ruin-crossing Lévy marks into finite-intensity negative tail
-- statement:
--   Uniform original spectrally negative finite-cap infinite-activity ruin-overshoot mark intensity localisation with no arbitrary cutoff parameter. Given finite positive C and the exact quadratic Lévy truncated-square energy condition, set δ=min(C.toReal,1)>0. Every mark that ruins an above-cap premark reserve y>C.toReal necessarily lies in the large negative-mark tail Iic(-δ). The already Proved finite-tail theorem gives ν of that set finite. This does not assume a first moment or finite expected ruin overshoot; it precisely separates the finite *number/rate* of ruin-crossing large jumps from the infinite-activity compensated small marks needed in the original stopped Itô source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mix_inf20_original_finitecap_automatic_ruin_crossing_tail_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : (∫⁻ z : ℝ,
      ENNReal.ofReal (min (1 : ℝ) (z ^ 2)) ∂X.ν) < ⊤)
    (C : ℝ≥0∞) (hFinite : C ≠ ⊤) (hCapPos : 0 < C.toReal)
    (y : ℝ) (hy : C.toReal < y) :
    X.ν {z : ℝ | y + z < 0} < ⊤ := by sorry
