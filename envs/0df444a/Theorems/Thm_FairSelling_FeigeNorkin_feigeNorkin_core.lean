-- Prove2me | Theorems.Thm_FairSelling_FeigeNorkin_feigeNorkin_core
-- name    : FairSelling.FeigeNorkin.feigeNorkin_core
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:15:03.436083+00:00
-- url     : https://prove2.me/theorems/a47cbac6-9598-4742-b54c-420a630946bb
-- title:
--   Feige Norkin: feige Norkin core
-- statement:
--   **The Feige–Norkin negative example.**  For every allocation of the eight goods to the
--   three agents, some agent `i` receives a bundle worth at most `33`, that is, at most `11/12`
--   of her target value `36`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkin.lean#L70-L77
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkin.lean#L70-L77

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkin
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.FeigeNorkin

theorem FairSelling.FeigeNorkin.feigeNorkin_core (f : Fin 8 → Fin 3) :
    ∃ i : Fin 3, (∑ j, if f j = i then fnW i j else 0) ≤ 33 := by sorry
