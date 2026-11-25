-- Prove2me | Theorems.Thm_DiracCycle_splice
-- name    : DiracCycle.splice
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:47:58.312367+00:00
-- url     : https://prove2.me/theorems/1f33bc8e-d45b-4c46-832e-83cda23d6ac9
-- title:
--   Dirac Cycle: splice
-- statement:
--   Splice: replace the cyclic arc from `f 0` to `f d` by a path `Q` whose interior is off the
--   cycle. The new cycle contains `Q` and the arc `f d, …, f m`.
--
--   Source: https://github.com/jtraverso/dirac-common-cycle/blob/3c9e9966662cb99c0e4f11d771011bc904dc627f/DiracCycleLib/DiracCycle.lean#L38-L118
-- source:
--   https://github.com/jtraverso/dirac-common-cycle/blob/3c9e9966662cb99c0e4f11d771011bc904dc627f/DiracCycleLib/DiracCycle.lean#L38-L118

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

theorem DiracCycle.splice {m : ℕ} {f : ℕ → V} (hC : CycArr G m f) {d : ℕ} (hd1 : 1 ≤ d) (hdm : d < m)
    (Q : G.Walk (f 0) (f d)) (hQ : Q.IsPath) (hQl : 2 ≤ Q.length)
    (hint : ∀ y ∈ Q.support, ∀ i, f i = y → y = f 0 ∨ y = f d) :
    ∃ m' g, CycArr G m' g ∧ (∀ y ∈ Q.support, ∃ i, g i = y) ∧
      ∀ i, d ≤ i → i ≤ m → ∃ j, g j = f i := by sorry
