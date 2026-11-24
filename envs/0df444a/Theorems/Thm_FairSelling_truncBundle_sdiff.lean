-- Prove2me | Theorems.Thm_FairSelling_truncBundle_sdiff
-- name    : FairSelling.truncBundle_sdiff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:25:55.929885+00:00
-- url     : https://prove2.me/theorems/b1babc23-3a23-418b-bd9b-a1dc7c206d67
-- title:
--   Fair Selling: trunc Bundle sdiff
-- statement:
--   The Fair Selling construction uses the trunc Bundle sdiff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSApprox.lean#L72-L74
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSApprox.lean#L72-L74

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G]

theorem FairSelling.truncBundle_sdiff (w p : G → ℝ) (t : ℝ) {R X : Finset G} (h : X ⊆ R) :
    truncBundle w p t R = truncBundle w p t (R \ X) + truncBundle w p t X := by sorry
