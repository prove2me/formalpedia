-- Prove2me | Theorems.Thm_FairSelling_le_TPS_of_le_truncSum
-- name    : FairSelling.le_TPS_of_le_truncSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:25:34.446343+00:00
-- url     : https://prove2.me/theorems/7257eeb6-5941-4abd-9aec-c74dec8b181d
-- title:
--   Fair Selling: le TPS of le trunc Sum
-- statement:
--   **Claim E** of the manuscript: if `f(t) ≥ t` for some `t`, then `TPS ≥ t`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSCompute.lean#L42-L44
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSCompute.lean#L42-L44

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]

theorem FairSelling.le_TPS_of_le_truncSum (v p : G → ℝ) {t : ℝ} (ht : t ≤ truncSum n v p t) :
    t ≤ TPS n v p := by sorry
