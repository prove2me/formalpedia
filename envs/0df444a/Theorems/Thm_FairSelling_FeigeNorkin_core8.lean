-- Prove2me | Theorems.Thm_FairSelling_FeigeNorkin_core8
-- name    : FairSelling.FeigeNorkin.core8
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:15:04.902552+00:00
-- url     : https://prove2.me/theorems/dee2b0a7-2ddf-42ac-a749-3593c3a0cc5b
-- title:
--   Feige Norkin: core8
-- statement:
--   The exhaustive check over all `3^8` assignments: in every assignment of the eight goods
--   to the three agents, one of them receives at most `33` (i.e. `11` before the scaling by `3`).
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkin.lean#L63-L65
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkin.lean#L63-L65

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkin
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.FeigeNorkin
set_option maxRecDepth 40000

theorem FairSelling.FeigeNorkin.core8 : ∀ a b c d e f g h : Fin 3,
    valOf fnR 0 a b c d e f g h ≤ 33 ∨ valOf fnC 1 a b c d e f g h ≤ 33 ∨
      valOf fnU 2 a b c d e f g h ≤ 33 := by sorry
