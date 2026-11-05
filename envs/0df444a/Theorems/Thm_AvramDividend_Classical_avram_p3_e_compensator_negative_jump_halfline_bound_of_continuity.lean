-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_negative_jump_halfline_bound_of_continuity
-- name    : AvramDividend.Classical.avram_p3_e_compensator_negative_jump_halfline_bound_of_continuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:59:36.395178+00:00
-- url     : https://prove2.me/theorems/e73782a4-331c-4702-8374-1019d234e374
-- title:
--   A negative-jump half-line bound from right-sided continuity and vanishing below zero
-- statement:
--   For the original Avram reserve verification, a value function continuous on the nonnegative half-line and identically zero on the negative half-line has a uniform absolute bound on every half-line (-∞,b]. This supplies the nonlinear stopped jump-compensator's global negative-jump envelope without an additional boundedness hypothesis.
-- source:
--   Elementary compactness and the maximum theorem for continuous functions on [0,max(b,0)]; zero-extension for negative reserve values. Intended input to source-exact original BV compensated jump theorem 8dda0d29-ac4a-4c35-87de-498bfca2df2a. No clock/predictability theorem is assumed or replaced.

import Mathlib
open Set Topology
noncomputable section

theorem AvramDividend.Classical.avram_p3_e_compensator_negative_jump_halfline_bound_of_continuity
(w : ℝ → ℝ) (hw_cont : ContinuousOn w (Set.Ici 0))
(hw_neg : ∀ y : ℝ, y < 0 → w y = 0) (b : ℝ) :
∃ R : ℝ, 0 ≤ R ∧ ∀ v : ℝ, v ≤ b → |w v| ≤ R := by sorry
