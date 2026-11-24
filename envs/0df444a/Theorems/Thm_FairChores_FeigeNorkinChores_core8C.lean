-- Prove2me | Theorems.Thm_FairChores_FeigeNorkinChores_core8C
-- name    : FairChores.FeigeNorkinChores.core8C
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:21:37.941522+00:00
-- url     : https://prove2.me/theorems/7859433f-5ec2-4ed5-8f03-4425cc19f7ed
-- title:
--   Feige Norkin Chores: core8 C
-- statement:
--   The exhaustive check over all `3^8` assignments: in every assignment of the eight chores
--   to the three agents, one of them incurs a cost of at least `380` (i.e. `19` before the
--   scaling by `20`).
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkinChores.lean#L66-L68
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkinChores.lean#L66-L68

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkinChores
set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.FeigeNorkinChores
set_option maxRecDepth 40000

theorem FairChores.FeigeNorkinChores.core8C : ∀ a b c d e f g h : Fin 3,
    380 ≤ costOf fcR 0 a b c d e f g h ∨ 380 ≤ costOf fcC 1 a b c d e f g h ∨
      380 ≤ costOf fcU 2 a b c d e f g h := by sorry
