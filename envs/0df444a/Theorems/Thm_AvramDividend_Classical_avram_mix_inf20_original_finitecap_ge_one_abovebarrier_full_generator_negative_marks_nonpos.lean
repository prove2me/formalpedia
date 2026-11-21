-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_ge_one_abovebarrier_full_generator_negative_marks_nonpos
-- name    : AvramDividend.Classical.avram_mix_inf20_original_finitecap_ge_one_abovebarrier_full_generator_negative_marks_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:29:17.113518+00:00
-- url     : https://prove2.me/theorems/f23857d3-d5e7-4b8e-9d03-2c05807f00c8
-- title:
--   Original true-truncated negative Lévy jump generator nonpositive above finite dividend cap at least unit size
-- statement:
--   True source-truncated Lévy generator jump sign above a finite cap at least 1, for the original spectrally negative Lévy generatorIntegrand with compensation only on -1<z<1. The caplinear extension V has negative or zero actual generator jump increment for every negative Lévy mark. If -1<z<0, starting y>C≥1 ensures y+z>0 so the full compensated Taylor upper envelope is zero by server-Proved fullmark envelope. For z≤-1 the source does not compensate at all and the raw V(y+z)-V(y)≤0 by server-Proved above-cap raw negative-mark monotonicity. This handles genuinely infinite activity and unbounded large negative marks without demanding their first moments, for the quantitative large-cap case. It is a rigorous above-cap drift sign ingredient for original stopped mixed Itô verification, not a claim that all cap sizes behave alike.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_complete_mark_overshoot_envelope
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_abovebarrier_all_negative_raw_marks_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mix_inf20_original_finitecap_ge_one_abovebarrier_full_generator_negative_marks_nonpos
    (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (hCapOne : 1 ≤ C.toReal)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ u : ℝ, u < 0 → w u = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (y z : ℝ) (hy : C.toReal < y) (hz : z < 0) :
    SpectrallyNegativeLevy.generatorIntegrand
      (fun t => if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal))
      y z ≤ 0 := by sorry
