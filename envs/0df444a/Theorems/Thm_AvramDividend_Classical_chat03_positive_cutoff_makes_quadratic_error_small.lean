-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_positive_cutoff_makes_quadratic_error_small
-- name    : AvramDividend.Classical.chat03_positive_cutoff_makes_quadratic_error_small
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:11:29.302721+00:00
-- url     : https://prove2.me/theorems/8f7b9076-2298-4276-882e-34ff52546b1c
-- title:
--   Positive clipping scale making the moment tail arbitrarily small
-- statement:
--   For any nonnegative real quadratic moment bound and positive tolerance, there exists a positive clipping threshold whose quadratic-tail ratio is at most the tolerance. The explicit threshold is (C+1)/epsilon.
-- source:
--   Positive real division and elementary arithmetic.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

theorem AvramDividend.Classical.chat03_positive_cutoff_makes_quadratic_error_small
    (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ C / R ≤ ε := by sorry
