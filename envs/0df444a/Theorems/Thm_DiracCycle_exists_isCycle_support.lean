-- Prove2me | Theorems.Thm_DiracCycle_exists_isCycle_support
-- name    : DiracCycle.exists_isCycle_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:48:04.126072+00:00
-- url     : https://prove2.me/theorems/72f889d2-02cb-5568-96c9-22529e38f1d5
-- title:
--   Dirac Cycle: exists is Cycle support
-- statement:
--   A cyclic arrangement gives a Mathlib cycle through all its vertices.
--
--   Source: https://github.com/jtraverso/dirac-common-cycle/blob/3c9e9966662cb99c0e4f11d771011bc904dc627f/DiracCycleLib/DiracCycle.lean#L224-L260
-- source:
--   https://github.com/jtraverso/dirac-common-cycle/blob/3c9e9966662cb99c0e4f11d771011bc904dc627f/DiracCycleLib/DiracCycle.lean#L224-L260

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

theorem DiracCycle.exists_isCycle_support {m : ℕ} {f : ℕ → V} (h : CycArr G m f) :
    ∃ c : G.Walk (f 0) (f 0), c.IsCycle ∧ ∀ i, f i ∈ c.support := by sorry
