-- Prove2me | Theorems.Thm_FairSelling_MMSEP_le_MMS
-- name    : FairSelling.MMSEP_le_MMS
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:23:16.813791+00:00
-- url     : https://prove2.me/theorems/b61d6ce2-2e1e-4dc3-abb0-0403818b8835
-- title:
--   Fair Selling: MMSEP le MMS
-- statement:
--   **The equal-proceeds MMS is at most the unconstrained MMS.**  ("Clearly, with this
--   requirement, the MMS value of agents is weakly smaller than without this requirement.")
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceeds.lean#L97-L100
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceeds.lean#L97-L100

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EqualProceeds
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.MMSEP_le_MMS (v p : G → ℝ) (hn : 0 < n) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    MMSEP n v p ≤ MMS n v p := by sorry
