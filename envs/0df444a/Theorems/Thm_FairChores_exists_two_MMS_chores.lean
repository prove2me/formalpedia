-- Prove2me | Theorems.Thm_FairChores_exists_two_MMS_chores
-- name    : FairChores.exists_two_MMS_chores
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:24:22.788146+00:00
-- url     : https://prove2.me/theorems/2ac30d8b-96c4-48e0-be1e-1d41c75b53d6
-- title:
--   Fair Chores: exists two MMS chores
-- statement:
--   **Theorem 5 (existence half) / Lemma 18 of the manuscript.**  Every instance of chores
--   with optional outsourcing admits a feasible outcome in which every agent's cost is at most
--   twice its maximin share.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresMMSApprox.lean#L55-L115
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresMMSApprox.lean#L55-L115

import Mathlib
import Definitions.Def_RequestProject_ChoresBagFilling
import Definitions.Def_RequestProject_ChoresMMSApprox
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}

theorem FairChores.exists_two_MMS_chores (hn : 0 < n) (c : Fin n → T → ℝ) (p : T → ℝ)
    (hc : ∀ i t, 0 ≤ c i t) (hp : ∀ t, 0 ≤ p t) :
    ∃ o : Outcome T n, o.Valid p ∧ ∀ i, cost (c i) o i ≤ 2 * MMS n (c i) p := by sorry
