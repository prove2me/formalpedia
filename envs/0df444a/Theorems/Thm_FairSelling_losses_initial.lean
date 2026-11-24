-- Prove2me | Theorems.Thm_FairSelling_losses_initial
-- name    : FairSelling.losses_initial
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:10:53.752301+00:00
-- url     : https://prove2.me/theorems/992f1396-848e-445b-ba1d-0ac839a1f0c2
-- title:
--   Fair Selling: losses initial
-- statement:
--   At the start of the algorithm nothing has been allocated, and the state is accounted for by
--   the empty history.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsLoss.lean#L146-L154
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsLoss.lean#L146-L154

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_EquiMMS
import Definitions.Def_RequestProject_TwoThirdsLoss
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.losses_initial (v : Fin n → G → ℝ) (p : G → ℝ)
    (hE : ∀ i, Nonempty (EquiMMS (v i) p (MMS n (v i) p) n)) :
    Losses v p Finset.univ Finset.univ (0 : ℝ) := by sorry
