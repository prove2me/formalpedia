-- Prove2me | Theorems.Thm_FairSelling_FeigeNorkin_fnC_partition
-- name    : FairSelling.FeigeNorkin.fnC_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:18:17.943655+00:00
-- url     : https://prove2.me/theorems/340c85c3-b839-45bc-b2da-4eb13da17cdf
-- title:
--   Feige Norkin: fn C partition
-- statement:
--   Agent `C` can split the goods into three bundles worth `36` each.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkin.lean#L138-L142
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkin.lean#L138-L142

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkin
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.FeigeNorkin

theorem FairSelling.FeigeNorkin.fnC_partition :
    (∑ j ∈ ({2, 5} : Finset (Fin 8)), fnC j) = 36 ∧
    (∑ j ∈ ({0, 3, 6} : Finset (Fin 8)), fnC j) = 36 ∧
    (∑ j ∈ ({1, 4, 7} : Finset (Fin 8)), fnC j) = 36 := by sorry
