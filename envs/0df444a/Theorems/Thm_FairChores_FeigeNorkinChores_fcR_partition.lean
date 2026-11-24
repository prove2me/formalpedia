-- Prove2me | Theorems.Thm_FairChores_FeigeNorkinChores_fcR_partition
-- name    : FairChores.FeigeNorkinChores.fcR_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:28:07.22844+00:00
-- url     : https://prove2.me/theorems/a7833204-a918-4e48-bc09-8bfafd04449b
-- title:
--   Feige Norkin Chores: fc R partition
-- statement:
--   Agent `R` can split the chores into three bundles costing `360` each, so her maximin
--   share is `360` (i.e. `18` before scaling).
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkinChores.lean#L114-L118
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkinChores.lean#L114-L118

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkinChores
set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.FeigeNorkinChores

theorem FairChores.FeigeNorkinChores.fcR_partition :
    (∑ j ∈ ({2, 3, 4} : Finset (Fin 8)), fcR j) = 360 ∧
    (∑ j ∈ ({0, 1} : Finset (Fin 8)), fcR j) = 360 ∧
    (∑ j ∈ ({5, 6, 7} : Finset (Fin 8)), fcR j) = 360 := by sorry
