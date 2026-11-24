-- Prove2me | Theorems.Thm_FairChores_FeigeNorkinChores_two_fcU_dominates
-- name    : FairChores.FeigeNorkinChores.two_fcU_dominates
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:48:06.995699+00:00
-- url     : https://prove2.me/theorems/2aaff085-28e3-4276-8618-2d42aefa71be
-- title:
--   Feige Norkin Chores: two fc U dominates
-- statement:
--   Twice agent `U`'s cost dominates the costs of the two other agents, chore by chore: this
--   is what makes outsourcing at prices proportional to `cU` (with a large factor) useless for
--   agents `R` and `C`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkinChores.lean#L140-L140
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkinChores.lean#L140-L140

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkinChores
set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.FeigeNorkinChores

theorem FairChores.FeigeNorkinChores.two_fcU_dominates : ∀ j : Fin 8, fcR j ≤ 2 * fcU j ∧ fcC j ≤ 2 * fcU j := by sorry
