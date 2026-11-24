-- Prove2me | Theorems.Thm_FairSelling_truncBundle_le_vbarSum
-- name    : FairSelling.truncBundle_le_vbarSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:25:36.48986+00:00
-- url     : https://prove2.me/theorems/eecc3c11-a18e-4482-8441-d1b91aea523d
-- title:
--   Fair Selling: trunc Bundle le vbar Sum
-- statement:
--   The Fair Selling construction uses the trunc Bundle le vbar Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSApprox.lean#L62-L64
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSApprox.lean#L62-L64

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

theorem FairSelling.truncBundle_le_vbarSum (w p : G → ℝ) (t : ℝ) (R : Finset G) :
    truncBundle w p t R ≤ vbarSum w p R := by sorry
