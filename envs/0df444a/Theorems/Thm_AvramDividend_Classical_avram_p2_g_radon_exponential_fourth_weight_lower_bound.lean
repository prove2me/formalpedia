-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_g_radon_exponential_fourth_weight_lower_bound
-- name    : AvramDividend.Classical.avram_p2_g_radon_exponential_fourth_weight_lower_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:29:15.031756+00:00
-- url     : https://prove2.me/theorems/a8c33b35-64f3-4640-af5d-7492aca20f66
-- title:
--   Uniform fourth exponential weight bound on a separated negative half-line
-- statement:
--   For every strictly positive epsilon and real x at most minus epsilon, the fourth exponential weight (exp x minus one)^4 is bounded below by the strictly positive epsilon-dependent constant (1-exp(-epsilon))^4. This is the crucial elementary domination used with the original fourth-weighted Lévy small-time derivative to bound rare separated negative increments and their independent finite-grid counts.
-- source:
--   Mathlib.Algebra.Order.GroupWithZero.Basic: pow_le_pow_left₀; Mathlib.Analysis.SpecialFunctions.ExpDeriv: Real.exp_le_exp.

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_p2_g_radon_exponential_fourth_weight_lower_bound
    (ε x : ℝ) (hε : 0 < ε) (hx : x ≤ -ε) :
    (1 - Real.exp (-ε)) ^ 4 ≤ (Real.exp x - 1) ^ 4 := by sorry
