-- Prove2me | Theorems.Thm_FairChores_waterfilling_iff_delta
-- name    : FairChores.waterfilling_iff_delta
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:22:16.251101+00:00
-- url     : https://prove2.me/theorems/bfbe5b4b-31ed-4e07-b69a-955868580eb0
-- title:
--   Fair Chores: waterfilling iff delta
-- statement:
--   **The water-filling derivation**: for a chore `t` of agent `i`'s bundle `Bᵢ`, outsourcing
--   `t` and splitting the resulting total cost equally between `Bᵢ \ {t}` and `B_j` is no
--   improvement over `Bᵢ` exactly when the outsourcing delta `p(t) − c̄ᵢ(t)` covers agent `i`'s
--   envy towards `B_j`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresEnvy.lean#L173-L177
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ChoresEnvy.lean#L173-L177

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy
set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable {ci p : T → ℝ}
omit [Fintype T]

theorem FairChores.waterfilling_iff_delta {Bi Bj : Finset T} {t : T} (ht : t ∈ Bi) :
    (cbarSum ci p (Bi \ {t}) + cbarSum ci p Bj + p t) / 2 ≥ cbarSum ci p Bi ↔
      p t - cbar ci p t ≥ cbarSum ci p Bi - cbarSum ci p Bj := by sorry
