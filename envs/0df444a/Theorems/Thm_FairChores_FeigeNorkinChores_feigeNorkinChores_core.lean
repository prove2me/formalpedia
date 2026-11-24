-- Prove2me | Theorems.Thm_FairChores_FeigeNorkinChores_feigeNorkinChores_core
-- name    : FairChores.FeigeNorkinChores.feigeNorkinChores_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:21:47.558588+00:00
-- url     : https://prove2.me/theorems/5c5af640-3f4a-492d-86ec-df7b9f240d99
-- title:
--   Feige Norkin Chores: feige Norkin Chores core
-- statement:
--   **The Feige–Norkin negative example for chores.**  For every allocation of the eight
--   chores to the three agents, some agent `i` incurs a cost of at least `380`, that is, at least
--   `19/18` of her target `360`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkinChores.lean#L73-L80
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkinChores.lean#L73-L80

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkinChores
set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.FeigeNorkinChores

theorem FairChores.FeigeNorkinChores.feigeNorkinChores_core (f : Fin 8 → Fin 3) :
    ∃ i : Fin 3, 380 ≤ (∑ j, if f j = i then fcW i j else 0) := by sorry
