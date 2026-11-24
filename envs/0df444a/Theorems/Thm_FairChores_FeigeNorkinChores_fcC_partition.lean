-- Prove2me | Theorems.Thm_FairChores_FeigeNorkinChores_fcC_partition
-- name    : FairChores.FeigeNorkinChores.fcC_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:27:59.505601+00:00
-- url     : https://prove2.me/theorems/268247d9-dd76-41b8-b4be-caae38f95ef4
-- title:
--   Feige Norkin Chores: fc C partition
-- statement:
--   Agent `C` can split the chores into three bundles costing `360` each.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkinChores.lean#L121-L125
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkinChores.lean#L121-L125

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkinChores
set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.FeigeNorkinChores

theorem FairChores.FeigeNorkinChores.fcC_partition :
    (∑ j ∈ ({2, 5} : Finset (Fin 8)), fcC j) = 360 ∧
    (∑ j ∈ ({0, 3, 6} : Finset (Fin 8)), fcC j) = 360 ∧
    (∑ j ∈ ({1, 4, 7} : Finset (Fin 8)), fcC j) = 360 := by sorry
