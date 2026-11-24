-- Prove2me | Theorems.Thm_FairChores_cbar_eq_zero_of_MMS_eq_zero
-- name    : FairChores.cbar_eq_zero_of_MMS_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:19:36.02794+00:00
-- url     : https://prove2.me/theorems/d3273c8e-bbc1-46f8-b9bb-4c19f2ca7268
-- title:
--   Fair Chores: cbar eq zero of MMS eq zero
-- statement:
--   An agent whose maximin share is `0` can perform (or pay for) every chore at no cost.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresMMSApprox.lean#L32-L50
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresMMSApprox.lean#L32-L50

import Mathlib
import Definitions.Def_RequestProject_ChoresBagFilling
import Definitions.Def_RequestProject_ChoresMMSApprox
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}

theorem FairChores.cbar_eq_zero_of_MMS_eq_zero {c p : T → ℝ} (hc : ∀ t, 0 ≤ c t) (hp : ∀ t, 0 ≤ p t)
    (hn : 0 < n) (h0 : MMS n c p = 0) (t : T) : cbar c p t = 0 := by sorry
