-- Prove2me | Theorems.Thm_FairSelling_TPS_nonneg
-- name    : FairSelling.TPS_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:10:36.228244+00:00
-- url     : https://prove2.me/theorems/5ab2922c-d1e0-447b-bd46-a9e2d9ec9214
-- title:
--   Fair Selling: TPS nonneg
-- statement:
--   `TPS` is nonnegative (prices being nonnegative).
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSCompute.lean#L48-L49
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSCompute.lean#L48-L49

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]

theorem FairSelling.TPS_nonneg (v p : G → ℝ) (hp : ∀ g, 0 ≤ p g) : 0 ≤ TPS n v p := by sorry
