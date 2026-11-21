-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_abovecap_true_truncated_jump_positive_tail_unit_domination
-- name    : AvramDividend.Classical.avram_mix_inf20_original_abovecap_true_truncated_jump_positive_tail_unit_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:30:26.977005+00:00
-- url     : https://prove2.me/theorems/15371b4c-eb66-4507-a365-a0d0b10b757e
-- title:
--   Original exact-truncated finitecap Lévy generator positive contribution dominated by unit finite-intensity negative tail
-- statement:
--   Source-faithful original Lévy upper-cap infinite-jump compensation bound with correct indicator truncation. For any C finite, 0<δ≤min(C.toReal,1), y>C and negative mark z, the positive part of the genuine SpectrallyNegativeLevy.generatorIntegrand caplinear potential is dominated by the unit indicator of large marks z≤-δ. Small compensated marks z>-δ cannot overshoot below zero, so the Taylor remainder is nonpositive. If -1<z≤-δ causes ruin, its positive overshoot is <1 since the premark reserve y>0 and |z|<1. Marks z≤-1 use raw value difference without derivative compensation and are nonpositive. Therefore the only positive source is uniformly bounded and supported on a Lévy finite-intensity tail (Proved 3e5bbc19). This resolves the heavy negative-mark first moment issue of full linear compensation; it is a deterministic bound with the exact generatorIntegrand, not an assertion of global stochastic Itô convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_complete_mark_overshoot_envelope
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_abovebarrier_all_negative_raw_marks_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mix_inf20_original_abovecap_true_truncated_jump_positive_tail_unit_domination
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
    (hy : C.toReal < y) (hz : z < 0) :
    SpectrallyNegativeLevy.generatorIntegrand
      (fun t => if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal))
      y z ≤ if z ≤ -δ then 1 else 0 := by sorry
