-- Prove2me | Theorems.Thm_FairSelling_SharedProceeds_sharing_needed
-- name    : FairSelling.SharedProceeds.sharing_needed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:55:47.994393+00:00
-- url     : https://prove2.me/theorems/b36fab9a-aab4-4e7d-9013-110a6c0594f5
-- title:
--   Shared Proceeds: sharing needed
-- statement:
--   **Sale proceeds have to be shared.**  In every valid outcome for this instance that gives
--   both agents the guarantee `13/3 = (2/3)·TPS`, the good `g₀` is sold and both agents hold at least
--   `4/3` of its proceeds.  In particular no assignment of the sold good to a single "owner" can make
--   that owner able to buy the good back.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxSharing.lean#L94-L137
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxSharing.lean#L94-L137

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxSharing
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.SharedProceeds

theorem FairSelling.SharedProceeds.sharing_needed (o : Outcome (Fin 4) 2) (hvalid : o.Valid sp)
    (hutil : ∀ i, (13 : ℝ) / 3 ≤ util sv o i) :
    (0 : Fin 4) ∈ o.sold ∧ ∀ i, (4 : ℝ) / 3 ≤ o.money i := by sorry
