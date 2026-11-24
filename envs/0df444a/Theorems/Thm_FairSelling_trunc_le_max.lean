-- Prove2me | Theorems.Thm_FairSelling_trunc_le_max
-- name    : FairSelling.trunc_le_max
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:27:11.857164+00:00
-- url     : https://prove2.me/theorems/b97e9d86-9f90-49cc-b343-819c4e4c2b51
-- title:
--   Fair Selling: trunc le max
-- statement:
--   The Fair Selling construction uses the trunc le max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSApprox.lean#L54-L55
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSApprox.lean#L54-L55

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G] [DecidableEq G]

theorem FairSelling.trunc_le_max (w p : G → ℝ) (t : ℝ) (g : G) : trunc w p t g ≤ max (p g) t := by sorry
