-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_geometric_budget_lt_top_of_ratio_lt_one
-- name    : AvramDividend.Classical.chat12_geometric_budget_lt_top_of_ratio_lt_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T18:46:39.007207+00:00
-- url     : https://prove2.me/theorems/cca71d4b-7e4a-45f9-8eeb-8ecc2f34d022
-- title:
--   Finiteness of discounted renewal geometric budget when exit factor is below one
-- statement:
--   For nonnegative ε and p with p strictly below one, the closed-form expected-record geometric upper budget ENNReal.ofReal ε multiplied by (1-ENNReal.ofReal p)^(-1) is finite in ENNReal. This provides the strict non-explosion property needed to use the conditional upper record budget in a finite valuation. Proof uses the exact revision-pinned ENNReal.ofReal_lt_one, tsub_pos_iff_lt, inv_lt_top and mul_lt_top lemmas.

import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations

open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat12_geometric_budget_lt_top_of_ratio_lt_one
    (ε p : ℝ) (hε : 0 ≤ ε) (hp : 0 ≤ p) (hp1 : p < 1) :
    ENNReal.ofReal ε * (1 - ENNReal.ofReal p)⁻¹ < ∞ := by sorry
