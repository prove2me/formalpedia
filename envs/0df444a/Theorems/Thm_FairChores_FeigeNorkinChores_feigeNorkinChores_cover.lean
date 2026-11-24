-- Prove2me | Theorems.Thm_FairChores_FeigeNorkinChores_feigeNorkinChores_cover
-- name    : FairChores.FeigeNorkinChores.feigeNorkinChores_cover
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:21:50.049138+00:00
-- url     : https://prove2.me/theorems/103aea85-ea88-45e1-85bf-9aec3399a7f3
-- title:
--   Feige Norkin Chores: feige Norkin Chores cover
-- statement:
--   Version of `feigeNorkinChores_core` for three bundles covering all the chores (chores,
--   unlike goods, must all be allocated — collective outsourcing is accounted for in the third
--   bundle).
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkinChores.lean#L85-L108
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkinChores.lean#L85-L108

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkinChores
set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.FeigeNorkinChores

theorem FairChores.FeigeNorkinChores.feigeNorkinChores_cover (A : Fin 3 → Finset (Fin 8))
    (hcov : ∀ j : Fin 8, j ∈ A 0 ∨ j ∈ A 1 ∨ j ∈ A 2) :
    ∃ i : Fin 3, 380 ≤ ∑ j ∈ A i, fcW i j := by sorry
