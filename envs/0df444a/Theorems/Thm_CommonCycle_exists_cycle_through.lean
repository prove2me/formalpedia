-- Prove2me | Theorems.Thm_CommonCycle_exists_cycle_through
-- name    : CommonCycle.exists_cycle_through
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:03:27.55883+00:00
-- url     : https://prove2.me/theorems/33b0659e-7eab-4e70-af91-d37bc282abf4
-- title:
--   Common Cycle: exists cycle through
-- statement:
--   **Dirac's theorem (1960).** In a `k`-connected finite graph with `k ≥ 2`, any set `S` of at
--   most `k` vertices lies on a common cycle.
--
--   Source: https://github.com/jtraverso/dirac-common-cycle/blob/3c9e9966662cb99c0e4f11d771011bc904dc627f/Solution.lean#L33-L37
-- source:
--   https://github.com/jtraverso/dirac-common-cycle/blob/3c9e9966662cb99c0e4f11d771011bc904dc627f/Solution.lean#L33-L37

module
public import Mathlib
public import Definitions.Def_DiracCycleLib_DiracCycle
public import Definitions.Def_DiracCommonCycle_Solution
public import Theorems.Thm_DiracCycle_exists_cycle_through

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open CommonCycle
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem CommonCycle.exists_cycle_through {k : ℕ} (hk : 2 ≤ k) (hn : k < Fintype.card V)
    (hconn : ∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected) (S : Finset V)
    (hS : #S ≤ k) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ ∀ x ∈ S, x ∈ c.support := by sorry
