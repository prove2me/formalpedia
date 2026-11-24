-- Prove2me | Theorems.Thm_FairSelling_FeigeNorkin_fnR_partition
-- name    : FairSelling.FeigeNorkin.fnR_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:18:13.817802+00:00
-- url     : https://prove2.me/theorems/5ecf8da8-38aa-4cff-878a-74f9efb9c9b5
-- title:
--   Feige Norkin: fn R partition
-- statement:
--   Agent `R` can split the goods into three bundles worth `36` each, so her maximin share
--   is `36` (i.e. `12` before scaling).
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkin.lean#L131-L135
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkin.lean#L131-L135

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkin
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.FeigeNorkin

theorem FairSelling.FeigeNorkin.fnR_partition :
    (∑ j ∈ ({2, 3, 4} : Finset (Fin 8)), fnR j) = 36 ∧
    (∑ j ∈ ({0, 1} : Finset (Fin 8)), fnR j) = 36 ∧
    (∑ j ∈ ({5, 6, 7} : Finset (Fin 8)), fnR j) = 36 := by sorry
