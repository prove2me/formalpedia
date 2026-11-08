-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gen10_affine_payoff_payout_jump
-- name    : AvramDividend.Classical.avram_gen10_affine_payoff_payout_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T11:07:37.987733+00:00
-- url     : https://prove2.me/theorems/20200c29-0a16-4556-9b3b-1d7634e0d704
-- title:
--   Affordable dividend right jumps satisfy affine positive-payoff inequality
-- statement:
--   For a nonnegative reserve r, an affordable nonnegative payout a that leaves a nonnegative reserve, the positive affine payoff w(y)=1+y for y≥0 gives w(r)−w(r−a)=a. This is the core HJB dividend-jump condition for the proposed generator nonintegrability countermodel.
-- source:
--   Original-process generator-integrability countermodel: scalar affine payoff condition used to discharge the jump-condition conjunct for the stochastic dividend strategy.

import Mathlib
open Classical
noncomputable section

theorem AvramDividend.Classical.avram_gen10_affine_payoff_payout_jump
    (r a : ℝ) (hr : 0 ≤ r) (ha : 0 ≤ a)
    (hpost : 0 ≤ r - a) :
    a ≤
      (if r < 0 then (0 : ℝ) else 1 + r) -
      (if r - a < 0 then (0 : ℝ) else 1 + (r - a)) := by sorry
