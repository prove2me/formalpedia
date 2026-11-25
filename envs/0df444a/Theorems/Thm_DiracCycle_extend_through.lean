-- Prove2me | Theorems.Thm_DiracCycle_extend_through
-- name    : DiracCycle.extend_through
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:48:40.76588+00:00
-- url     : https://prove2.me/theorems/247a8edc-2659-47a9-85c0-c7daa2358493
-- title:
--   Dirac Cycle: extend through
-- statement:
--   One induction step of Dirac's argument: a cycle containing `T` (with `f 0 ∈ T` if `T` is
--   nonempty) and a vertex `x` off it give a cycle containing `T` and `x`, provided `#T < k`.
--
--   Source: https://github.com/jtraverso/dirac-common-cycle/blob/3c9e9966662cb99c0e4f11d771011bc904dc627f/DiracCycleLib/DiracCycle.lean#L264-L350
-- source:
--   https://github.com/jtraverso/dirac-common-cycle/blob/3c9e9966662cb99c0e4f11d771011bc904dc627f/DiracCycleLib/DiracCycle.lean#L264-L350

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

theorem DiracCycle.extend_through [Finite V] {k : ℕ} (hk : 2 ≤ k)
    (hconn : ∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected)
    {m : ℕ} {f : ℕ → V} (hC : CycArr G m f) (T : Finset V) (hTk : #T < k)
    (hT0 : T.Nonempty → f 0 ∈ T) {x : V} (hx : ∀ i, f i ≠ x) :
    ∃ m' g, CycArr G m' g ∧ (∃ i, g i = x) ∧ ∀ p < m, f p ∈ T → ∃ i, g i = f p := by sorry
