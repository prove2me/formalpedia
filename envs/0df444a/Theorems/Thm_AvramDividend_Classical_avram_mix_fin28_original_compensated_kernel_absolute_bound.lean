-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin28_original_compensated_kernel_absolute_bound
-- name    : AvramDividend.Classical.avram_mix_fin28_original_compensated_kernel_absolute_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T15:05:54.655136+00:00
-- url     : https://prove2.me/theorems/0fafc6be-3657-4924-872f-4cad3c9f828a
-- title:
--   Original finite-mixed negative-mark compensated generator kernel has bounded absolute size
-- statement:
--   Under the original finite-cap mixed HJB reward regularity and gradient assumptions, for every positive reserve y below C and every negative mark z, the generator integrand w(y+z)-w(y)-z*1_{|z|<1}*w'(y) has absolute value at most w(y)+abs(w'(y)). Use the authoritative Proved mark-size-independent reward increment bound e8a2fc6a and the bounded size of the small-mark truncation. On a compact reserve strip [u,v), the right side is uniformly bounded by the already Proved original compact reward and derivative estimates, so finite negative-jump intensity yields an integrable compensation kernel without separately assuming E|large jump| finite. This feeds the direct physical child 52a16569 for 2545e563.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin27_original_negative_mark_reward_increment_bounded
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin28_original_compensated_kernel_absolute_bound
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ t < 0, w t = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {t : ℝ | 0 < t ∧ ENNReal.ofReal t < C})
    (hw_grad : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal t < C → 1 ≤ deriv w t)
    (y z : ℝ) (hy : 0 < y)
    (hyC : ENNReal.ofReal y < C) (hz : z < 0) :
    |SpectrallyNegativeLevy.generatorIntegrand w y z| ≤
      w y + |deriv w y| := by sorry
