-- Prove2me | Theorems.Thm_FairSelling_restrictVal_mem
-- name    : FairSelling.restrictVal_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:13:23.827967+00:00
-- url     : https://prove2.me/theorems/d5eabe3e-b11a-4a4b-8a91-2721279d0256
-- title:
--   Fair Selling: restrict Val mem
-- statement:
--   The Fair Selling construction uses the restrict Val mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L55-L56
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L55-L56

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

theorem FairSelling.restrictVal_mem (R : Finset G) (w : G → ℝ) {g : G} (hg : g ∈ R) :
    restrictVal R w g = w g := by sorry
