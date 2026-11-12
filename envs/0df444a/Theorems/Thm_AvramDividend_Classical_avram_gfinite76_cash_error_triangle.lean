-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite76_cash_error_triangle
-- name    : AvramDividend.Classical.avram_gfinite76_cash_error_triangle
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T07:58:26.227568+00:00
-- url     : https://prove2.me/theorems/2e137d7f-3d07-43e5-b6d7-dae49f0e0581
-- title:
--   Positive-part triangle inequality for a split cash residual
-- statement:
--   Any real cash error decomposed as an intermediate residual plus a mesh-remainder has positive part at most the sum of their positive parts. This isolates the original-process stochastic ledger from a separately controlled approximation error.

import Mathlib

theorem AvramDividend.Classical.avram_gfinite76_cash_error_triangle (a b c : ℝ) :
    max (a - c) 0 ≤ max (a - b) 0 + max (b - c) 0 := by
  sorry
