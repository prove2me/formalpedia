-- Prove2me | Theorems.Thm_FairSelling_MMS_liquid_le
-- name    : FairSelling.MMS_liquid_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:10:03.07981+00:00
-- url     : https://prove2.me/theorems/83a349e2-3f3b-4e06-a47b-c1736ec2da45
-- title:
--   Fair Selling: MMS liquid le
-- statement:
--   **The liquid value of a part is at most the maximin share.**  In an outcome all of whose parts
--   are worth at least the maximin share, the total *price* of the goods of a part, plus the money of
--   that part, never exceeds the maximin share.
--
--   Indeed, otherwise all the goods of that part could be sold, leaving that part with strictly more
--   than `MMS` in pure money, of which a small amount could be handed to each of the other parts;
--   every part would then be worth strictly more than `MMS`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EquiMMS.lean#L143-L230
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EquiMMS.lean#L143-L230

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_EquiMMS
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.MMS_liquid_le (hn : 0 < n) (v p : G → ℝ) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g)
    {o : Outcome G n} (hval : o.Valid p) (hge : ∀ j, MMS n v p ≤ util v o j) (j : Fin n) :
    (∑ g ∈ o.kept j, p g) + o.money j ≤ MMS n v p := by sorry
