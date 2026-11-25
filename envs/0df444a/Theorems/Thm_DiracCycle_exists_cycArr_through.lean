-- Prove2me | Theorems.Thm_DiracCycle_exists_cycArr_through
-- name    : DiracCycle.exists_cycArr_through
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:49:01.986814+00:00
-- url     : https://prove2.me/theorems/6c0271ed-b1e5-4f7d-b8e2-2785ecb108ad
-- title:
--   Dirac Cycle: exists cyc Arr through
-- statement:
--   Every set of at most `k` vertices lies on a common cyclic arrangement.
--
--   Source: https://github.com/jtraverso/dirac-common-cycle/blob/3c9e9966662cb99c0e4f11d771011bc904dc627f/DiracCycleLib/DiracCycle.lean#L353-L394
-- source:
--   https://github.com/jtraverso/dirac-common-cycle/blob/3c9e9966662cb99c0e4f11d771011bc904dc627f/DiracCycleLib/DiracCycle.lean#L353-L394

module
public import Mathlib
public import Definitions.Def_MengerHamilton_ChvatalErdosAux
public import Definitions.Def_DiracCycleLib_DiracCycle
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open DiracCycle
open Hamiltonicity
variable {V : Type*} {G : SimpleGraph V}

theorem DiracCycle.exists_cycArr_through [Fintype V] {k : ℕ} (hk : 2 ≤ k) (hn : k < Fintype.card V)
    (hconn : ∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected) (T : Finset V)
    (hT : #T ≤ k) : ∃ m f, CycArr G m f ∧ ∀ y ∈ T, ∃ i, f i = y := by sorry
