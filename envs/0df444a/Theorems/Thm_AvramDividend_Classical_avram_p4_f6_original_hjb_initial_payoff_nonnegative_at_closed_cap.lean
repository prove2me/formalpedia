-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f6_original_hjb_initial_payoff_nonnegative_at_closed_cap
-- name    : AvramDividend.Classical.avram_p4_f6_original_hjb_initial_payoff_nonnegative_at_closed_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:13:12.748095+00:00
-- url     : https://prove2.me/theorems/dcc85b03-8926-44f0-9cf4-6c08d02ce8c3
-- title:
--   Original UBV HJB candidate is nonnegative at any admissible starting reserve including cap contact
-- statement:
--   At positive original initial reserve x with ofReal x at most the extended cap C, HJB slope at least one in the strict interior and continuity at endpoints force w(x) nonnegative even when x is exactly C. This supplies the first conjunct of the original compact stopped source certificate without assuming interior start.
-- source:
--   Existing Proved closed-cap gradient lower-envelope theorem fc03f3ac plus C2 implies C1, and w(0) and x nonnegative.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope
open Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f6_original_hjb_initial_payoff_nonnegative_at_closed_cap
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) :
    0 ≤ w x := by sorry
