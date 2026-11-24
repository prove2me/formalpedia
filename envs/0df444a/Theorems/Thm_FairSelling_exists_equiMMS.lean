-- Prove2me | Theorems.Thm_FairSelling_exists_equiMMS
-- name    : FairSelling.exists_equiMMS
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:10:00.968961+00:00
-- url     : https://prove2.me/theorems/fcb3fe51-fdc9-46fc-a9be-e245fd8748b7
-- title:
--   Fair Selling: exists equi MMS
-- statement:
--   **Lemma 6 for a single agent.**  Every valuation can be lowered pointwise, without changing
--   the maximin share, so that the agent has an equi-valued MMS partition.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EquiMMS.lean#L236-L346
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EquiMMS.lean#L236-L346

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

theorem FairSelling.exists_equiMMS (hn : 0 < n) (v p : G → ℝ) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    ∃ w : G → ℝ, (∀ g, 0 ≤ w g) ∧ (∀ g, w g ≤ v g) ∧ MMS n w p = MMS n v p ∧
      Nonempty (EquiMMS w p (MMS n w p) n) := by sorry
