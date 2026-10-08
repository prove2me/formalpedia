-- Prove2me | Theorems.Thm_AvramDividend_Classical_exponential_dividend_lump_sum_gap
-- name    : AvramDividend.Classical.exponential_dividend_lump_sum_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:40:51.731622+00:00
-- url     : https://prove2.me/theorems/a6f1b0eb-83e2-4f16-b80e-a1bad4c9df8b
-- title:
--   An exponential test value drops by at least the dividend increment when θ≥1
-- statement:
--   For θ≥1, remaining reserves u≥0 and a nonnegative dividend increment d, the exponential test function satisfies d≤exp(θ(u+d))−exp(θu). This is a quantified lump-sum version of the dividend verification gradient condition w'≥1 and follows from exp z≥1+z and exp(θu)≥1.
-- source:
--   Pinned Mathlib Real.add_one_le_exp and Real.one_le_exp. Deterministic dividend-jump estimate used in Proposition 4 local verification.

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.exponential_dividend_lump_sum_gap
    (θ u d : ℝ) (hθ : 1 ≤ θ) (hu : 0 ≤ u) (hd : 0 ≤ d) :
    d ≤ Real.exp (θ * (u + d)) - Real.exp (θ * u) := by sorry
