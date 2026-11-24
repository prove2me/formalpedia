-- Prove2me | Theorems.Thm_FairSelling_reduction_budget
-- name    : FairSelling.reduction_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:15:20.121986+00:00
-- url     : https://prove2.me/theorems/fa62e178-2c9a-45a5-a0ea-a00f9c59128f
-- title:
--   Fair Selling: reduction budget
-- statement:
--   The value accounting of the pairing step, for `ρ = 2/3`: starting from `n₀ + n₂ + n₄` bundles
--   of value `μ` each, discounting the `ℓ₂` losses (at most `ρ·μ` each), the `ℓ₄` losses (at most `μ`
--   each) and the `t` new pure bundles (at most `2ρ·μ` each), at least `(n₀ − t)·μ` of value is
--   left.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsReduction.lean#L37-L42
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsReduction.lean#L37-L42

import Mathlib
import Definitions.Def_RequestProject_TwoThirdsReduction
set_option autoImplicit true
open FairSelling

theorem FairSelling.reduction_budget (μ : ℝ) (hμ : 0 ≤ μ) (n0 n2 n4 t : ℕ) (ht : t ≤ n2) (Gval : ℝ)
    (hG : ((n0 : ℝ) + n2 + n4) * μ - (n2 : ℝ) * ((2 / 3) * μ) - (n4 : ℝ) * μ
        - 2 * (t : ℝ) * ((2 / 3) * μ) ≤ Gval) :
    ((n0 : ℝ) - t) * μ ≤ Gval := by sorry
