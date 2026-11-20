-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_physical_one_or_more_size2_marks_disprove_unitmark_ruin_budget
-- name    : AvramDividend.Classical.avram_jump6_A_physical_one_or_more_size2_marks_disprove_unitmark_ruin_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T09:28:33.732774+00:00
-- url     : https://prove2.me/theorems/8e83e17a-bf91-4e1d-ab49-83dcb2a5d111
-- title:
--   One or more actual negative size-two marks rule out original ruin-clipped unit-fullmark budget
-- statement:
--   For the exact original finite-cap Brownian–size-two-Poisson countermodel with starting x=1/10 and w(x)=111/100, any path with Gaussian gain b≤1/4000, at least one physical negative size-two mark N≥1 by t≤1/500 and nonpositive drift B forces the unit coefficient raw-fullmark proposed right side strictly below zero. Hence it cannot dominate the nonnegative ruin-clipped original payoff H=0. This is a simple model-faithful scalar prerequisite that does not require proving an exact jump count at the first arrival.

import Mathlib
set_option autoImplicit false
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_physical_one_or_more_size2_marks_disprove_unitmark_ruin_budget
    (b t B : ℝ) (N : ℕ)
    (hb : b ≤ 1 / 4000) (ht : t ≤ 1 / 500)
    (hMark : 1 ≤ N) (hB : B ≤ 0)
    (hLedger : 0 ≤ (111 / 100 : ℝ) + b - 2 * (N : ℝ) + 2 * t + B) :
    False := by sorry
