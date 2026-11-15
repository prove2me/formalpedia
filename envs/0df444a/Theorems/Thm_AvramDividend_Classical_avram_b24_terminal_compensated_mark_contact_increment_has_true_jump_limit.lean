-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_terminal_compensated_mark_contact_increment_has_true_jump_limit
-- name    : AvramDividend.Classical.avram_b24_terminal_compensated_mark_contact_increment_has_true_jump_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:50:52.981203+00:00
-- url     : https://prove2.me/theorems/4236ce01-a82a-465c-8477-4eb6ca16b879
-- title:
--   True terminal compensated mark contact mesh tends to predictable weight times the surviving jump
-- statement:
--   For a càdlàg original compensated-mark path J, deterministic cells [a_k,b_k] that approach a ruin-contact time t from strict left and weak right, and bounded predictable weights converging to the left-contact weight, the weighted full-cell mark increment tends to the weight times the actual jump J(t)-J(t-). The terminal contact mark generally survives: it must enter the genuine negative ruin-crossing jump Itô-Meyer cash inequality. Prevents incorrectly setting the compensated terminal source to zero as with the continuous Gaussian channel.
-- source:
--   Left-limit/right-continuous terminal noise and Filter.Tendsto subtraction/multiplication in pinned Mathlib.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_terminal_compensated_mark_contact_increment_has_true_jump_limit
    (J : ℝ≥0 → ℝ) (t : ℝ≥0) (Jleft : ℝ)
    (a b : ℕ → ℝ≥0) (W : ℕ → ℝ) (Wleft : ℝ)
    (hRight : ContinuousWithinAt J (Ici t) t)
    (hLeft : Tendsto J (𝓝[<] t) (𝓝 Jleft))
    (ha : Tendsto a atTop (𝓝[<] t))
    (hb : Tendsto b atTop (𝓝[Ici t] t))
    (hW : Tendsto W atTop (𝓝 Wleft)) :
    Tendsto (fun k => W k * (J (b k) - J (a k))) atTop
      (𝓝 (Wleft * (J t - Jleft))) := by sorry
