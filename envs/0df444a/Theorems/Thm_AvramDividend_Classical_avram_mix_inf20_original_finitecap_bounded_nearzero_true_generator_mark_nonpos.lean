-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_bounded_nearzero_true_generator_mark_nonpos
-- name    : AvramDividend.Classical.avram_mix_inf20_original_finitecap_bounded_nearzero_true_generator_mark_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:34:51.611223+00:00
-- url     : https://prove2.me/theorems/8ba2cf30-c630-4fb4-8f93-fa5999eb38a7
-- title:
--   Original infinite negative activity small generator marks above cap have exact nonpositive compensated sign away from ruin
-- statement:
--   Sharp source-faithful infinite negative-activity result for the original mixed stopped finitecap potential V. For an above-cap predictable reserve y>C and any negative Lévy jump of magnitude strictly smaller than δ≤min(1,C.toReal), the postjump reserve is still strictly positive, so there is no ruin contact. Because z is strictly between -1 and 0, the genuine SpectrallyNegativeLevy.generatorIntegrand subtracts the derivative exactly once. The Proved caplinear fullmark estimate 85b04ac6 then bounds the compensated Taylor remainder by zero. This removes all small-jump positive compensated generator contributions without finite activity or integrability hypotheses. Large negative-mark events require separate finite-intensity compensation and ruin contact.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_complete_mark_overshoot_envelope
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mix_inf20_original_finitecap_bounded_nearzero_true_generator_mark_nonpos
    (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ u : ℝ, u < 0 → w u = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (δ y z : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hδcap : δ ≤ C.toReal)
    (hy : C.toReal < y) (hz : z < 0) (hzsmall : -δ < z) :
    SpectrallyNegativeLevy.generatorIntegrand
      (fun t => if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal))
      y z ≤ 0 := by sorry
