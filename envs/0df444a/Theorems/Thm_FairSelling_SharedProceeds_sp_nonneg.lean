-- Prove2me | Theorems.Thm_FairSelling_SharedProceeds_sp_nonneg
-- name    : FairSelling.SharedProceeds.sp_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:05:22.336871+00:00
-- url     : https://prove2.me/theorems/da1aa571-c5da-43db-861c-a186c4ae3453
-- title:
--   Shared Proceeds: sp nonneg
-- statement:
--   The Shared Proceeds construction uses the sp nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxSharing.lean#L54-L55
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxSharing.lean#L54-L55

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxSharing
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.SharedProceeds

theorem FairSelling.SharedProceeds.sp_nonneg : ∀ g, 0 ≤ sp g := by sorry
