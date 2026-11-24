-- Prove2me | Theorems.Thm_FairSelling_thr_nonneg
-- name    : FairSelling.thr_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:10:45.58687+00:00
-- url     : https://prove2.me/theorems/c2a9523c-1789-415c-8dee-d77f4611e810
-- title:
--   Fair Selling: thr nonneg
-- statement:
--   The Fair Selling construction uses the thr nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsLoss.lean#L50-L52
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsLoss.lean#L50-L52

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

theorem FairSelling.thr_nonneg (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n) (hv : ∀ i g, 0 ≤ v i g)
    (hp : ∀ g, 0 ≤ p g) (i : Fin n) : 0 ≤ thr v p i := by sorry
