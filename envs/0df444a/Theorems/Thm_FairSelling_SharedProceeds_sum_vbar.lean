-- Prove2me | Theorems.Thm_FairSelling_SharedProceeds_sum_vbar
-- name    : FairSelling.SharedProceeds.sum_vbar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:05:00.467247+00:00
-- url     : https://prove2.me/theorems/760b16f5-7c34-41ab-9388-ed56c53ba031
-- title:
--   Shared Proceeds: sum vbar
-- statement:
--   The Shared Proceeds construction uses the sum vbar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxSharing.lean#L60-L62
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxSharing.lean#L60-L62

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxSharing
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.SharedProceeds

theorem FairSelling.SharedProceeds.sum_vbar : ∑ g : Fin 4, max (sp g) (sv g) = 13 := by sorry
