-- Prove2me | Theorems.Thm_FairSelling_trunc_le_vbar
-- name    : FairSelling.trunc_le_vbar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:27:10.606284+00:00
-- url     : https://prove2.me/theorems/a2b3d80e-ca80-446c-93fa-ef079b72072b
-- title:
--   Fair Selling: trunc le vbar
-- statement:
--   The Fair Selling construction uses the trunc le vbar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSApprox.lean#L50-L51
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSApprox.lean#L50-L51

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

theorem FairSelling.trunc_le_vbar (w p : G → ℝ) (t : ℝ) (g : G) : trunc w p t g ≤ vbar w p g := by sorry
