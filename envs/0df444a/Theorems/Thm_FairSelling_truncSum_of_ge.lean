-- Prove2me | Theorems.Thm_FairSelling_truncSum_of_ge
-- name    : FairSelling.truncSum_of_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:37:56.405199+00:00
-- url     : https://prove2.me/theorems/2f58bc43-f78c-42c8-a4a7-ccdd63f5c8a8
-- title:
--   Fair Selling: trunc Sum of ge
-- statement:
--   If `t` is at least every value `v g`, then `f(t) = PS`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSCompute.lean#L118-L122
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSCompute.lean#L118-L122

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]

theorem FairSelling.truncSum_of_ge (v p : G → ℝ) {t : ℝ} (ht : ∀ g, v g ≤ t) :
    truncSum n v p t = PS n v p := by sorry
