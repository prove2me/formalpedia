-- Prove2me | Theorems.Thm_FairSelling_MMSEPset_nonempty
-- name    : FairSelling.MMSEPset_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:48:55.744458+00:00
-- url     : https://prove2.me/theorems/3d70ecbd-7d52-488b-bba3-ef0322fd3949
-- title:
--   Fair Selling: MMSEPset nonempty
-- statement:
--   The Fair Selling construction uses the MMSEPset nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceeds.lean#L54-L55
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceeds.lean#L54-L55

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EqualProceeds
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G] [DecidableEq G]

theorem FairSelling.MMSEPset_nonempty (v p : G → ℝ) : (MMSEPset n v p).Nonempty := by sorry
