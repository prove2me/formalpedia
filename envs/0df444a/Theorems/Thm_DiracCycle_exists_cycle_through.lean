-- Prove2me | Theorems.Thm_DiracCycle_exists_cycle_through
-- name    : DiracCycle.exists_cycle_through
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:46:40.415076+00:00
-- url     : https://prove2.me/theorems/e1b457db-14df-4f92-828c-9a8efb3668e9
-- title:
--   Dirac Cycle: exists cycle through
-- statement:
--   **Dirac's theorem (1960).** In a `k`-connected finite graph with `k ≥ 2`, any set `S` of at
--   most `k` vertices lies on a common cycle.
--
--   Source: https://github.com/jtraverso/dirac-common-cycle/blob/3c9e9966662cb99c0e4f11d771011bc904dc627f/DiracCycleLib/DiracCycle.lean#L402-L410
-- source:
--   https://github.com/jtraverso/dirac-common-cycle/blob/3c9e9966662cb99c0e4f11d771011bc904dc627f/DiracCycleLib/DiracCycle.lean#L402-L410

module
public import Mathlib
public import Definitions.Def_MengerHamilton_ChvatalErdosAux
public import Definitions.Def_DiracCycleLib_DiracCycle
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open DiracCycle
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem DiracCycle.exists_cycle_through {k : ℕ} (hk : 2 ≤ k) (hn : k < Fintype.card V)
    (hconn : ∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected) (S : Finset V)
    (hS : #S ≤ k) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ ∀ x ∈ S, x ∈ c.support := by sorry
