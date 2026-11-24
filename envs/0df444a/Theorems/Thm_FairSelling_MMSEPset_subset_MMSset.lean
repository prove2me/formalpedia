-- Prove2me | Theorems.Thm_FairSelling_MMSEPset_subset_MMSset
-- name    : FairSelling.MMSEPset_subset_MMSset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:36:09.570795+00:00
-- url     : https://prove2.me/theorems/83421aed-de03-4b64-90fe-4946bf830b0d
-- title:
--   Fair Selling: MMSEPset subset MMSset
-- statement:
--   The Fair Selling construction uses the MMSEPset subset MMSset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceeds.lean#L44-L46
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceeds.lean#L44-L46

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EqualProceeds
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G] [DecidableEq G]

theorem FairSelling.MMSEPset_subset_MMSset (v p : G → ℝ) : MMSEPset n v p ⊆ MMSset n v p := by sorry
