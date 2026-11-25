-- Prove2me | Theorems.Thm_CommonCycle_exists_cycle_through_pair
-- name    : CommonCycle.exists_cycle_through_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:05:24.261809+00:00
-- url     : https://prove2.me/theorems/283fbe85-296d-41e4-a643-9887ecd623a4
-- title:
--   Common Cycle: exists cycle through pair
-- statement:
--   In a `2`-connected finite graph, any two vertices lie on a common cycle.
--
--   Source: https://github.com/jtraverso/dirac-common-cycle/blob/3c9e9966662cb99c0e4f11d771011bc904dc627f/Solution.lean#L40-L43
-- source:
--   https://github.com/jtraverso/dirac-common-cycle/blob/3c9e9966662cb99c0e4f11d771011bc904dc627f/Solution.lean#L40-L43

module
public import Mathlib
public import Definitions.Def_DiracCycleLib_DiracCycle
public import Definitions.Def_DiracCommonCycle_Solution
public import Theorems.Thm_DiracCycle_exists_cycle_through_pair

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open CommonCycle
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem CommonCycle.exists_cycle_through_pair (hn : 2 < Fintype.card V)
    (hconn : ∀ S : Set V, S.ncard < 2 → (G.induce Sᶜ).Connected) (a b : V) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ a ∈ c.support ∧ b ∈ c.support := by sorry
