-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_ruin_crossing_marks_have_finite_levy_mass
-- name    : AvramDividend.Classical.avram_mix_inf20_original_finitecap_ruin_crossing_marks_have_finite_levy_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:20:36.262804+00:00
-- url     : https://prove2.me/theorems/ced6d3da-3c47-43f5-b4d4-3b76276b91b7
-- title:
--   Original finite-cap Lévy negative ruin-crossing marks have finite intensity under quadratic Lévy condition
-- statement:
--   True original Lévy finite-cap ruin-crossing intensity bridge in the infinite-negative-activity regime. A premark reserve y strictly above finite cap C cannot be ruined by any negative mark whose magnitude is below any positive δ≤min(1,C.toReal). The set of ruin-crossing marks {z | y+z<0} is contained in the negative Lévy tail Iic(-δ). The server-Proved quadratic Lévy measure finite-tail theorem gives X.ν Iic(-δ)<infinity from the actual standard truncated-square Lévy integrability premise. This establishes finite *intensity*, not an unjustified finite expected overshoot magnitude, and isolates large ruin marks from the infinite-activity small-jump compensated source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mix_inf20_original_finitecap_ruin_crossing_marks_have_finite_levy_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : (∫⁻ z : ℝ,
      ENNReal.ofReal (min (1 : ℝ) (z ^ 2)) ∂X.ν) < ⊤)
    (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hδcap : δ ≤ C.toReal)
    (y : ℝ) (hy : C.toReal < y) :
    X.ν {z : ℝ | y + z < 0} < ⊤ := by sorry
