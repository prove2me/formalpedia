-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f7_hjb_topcap_global_nonnegative
-- name    : AvramDividend.Classical.avram_p4_f7_hjb_topcap_global_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T10:27:47.072877+00:00
-- url     : https://prove2.me/theorems/8120a224-3834-43d9-8d62-d92c4d9762ba
-- title:
--   Top-cap HJB candidate value is globally nonnegative from right slope and negative extension
-- statement:
--   A reusable source-exact mathematical corollary for the original top-cap HJB supersolution: on the positive half-line, C2 interior differentiability, slope at least one, and continuity through zero imply monotonicity and nonnegativity from w(0)>=0; on the negative half-line w vanishes. The result provides a globally nonnegative discounted terminal integrand for the killed boundary reward comparison.

import Mathlib
open Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f7_hjb_topcap_global_nonnegative
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hTop : C = ⊤) :
    ∀ y : ℝ, 0 ≤ w y := by sorry
