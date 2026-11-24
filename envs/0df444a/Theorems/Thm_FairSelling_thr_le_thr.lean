-- Prove2me | Theorems.Thm_FairSelling_thr_le_thr
-- name    : FairSelling.thr_le_thr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:46:17.584464+00:00
-- url     : https://prove2.me/theorems/a9a580cb-a4f7-4504-86ab-abed1d0753c2
-- title:
--   Fair Selling: thr le thr
-- statement:
--   The Fair Selling construction uses the thr le thr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsLoss.lean#L55-L59
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsLoss.lean#L55-L59

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
omit [Fintype G] [DecidableEq G]

theorem FairSelling.thr_le_thr (v : Fin n → G → ℝ) (p : G → ℝ) {i j : Fin n}
    (h : MMS n (v i) p ≤ MMS n (v j) p) : thr v p i ≤ thr v p j := by sorry
