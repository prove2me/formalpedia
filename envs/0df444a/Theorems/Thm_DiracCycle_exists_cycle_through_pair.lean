-- Prove2me | Theorems.Thm_DiracCycle_exists_cycle_through_pair
-- name    : DiracCycle.exists_cycle_through_pair
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:46:32.839281+00:00
-- url     : https://prove2.me/theorems/b7b1231e-f971-5e3d-8ece-fddb756448c0
-- title:
--   Dirac Cycle: exists cycle through pair
-- statement:
--   In a `2`-connected finite graph, any two vertices lie on a common cycle.
--
--   Source: https://github.com/jtraverso/dirac-common-cycle/blob/3c9e9966662cb99c0e4f11d771011bc904dc627f/DiracCycleLib/DiracCycle.lean#L413-L418
-- source:
--   https://github.com/jtraverso/dirac-common-cycle/blob/3c9e9966662cb99c0e4f11d771011bc904dc627f/DiracCycleLib/DiracCycle.lean#L413-L418

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

theorem DiracCycle.exists_cycle_through_pair (hn : 2 < Fintype.card V)
    (hconn : ∀ S : Set V, S.ncard < 2 → (G.induce Sᶜ).Connected) (a b : V) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ a ∈ c.support ∧ b ∈ c.support := by sorry
