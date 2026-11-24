-- Prove2me | Theorems.Thm_FairSelling_restrictVal_nonneg
-- name    : FairSelling.restrictVal_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:23:40.82147+00:00
-- url     : https://prove2.me/theorems/df15100a-03bc-4422-9f09-51253ef9477d
-- title:
--   Fair Selling: restrict Val nonneg
-- statement:
--   The Fair Selling construction uses the restrict Val nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L59-L61
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L59-L61

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]

theorem FairSelling.restrictVal_nonneg (R : Finset G) {w : G → ℝ} (hw : ∀ g, 0 ≤ w g) (g : G) :
    0 ≤ restrictVal R w g := by sorry
