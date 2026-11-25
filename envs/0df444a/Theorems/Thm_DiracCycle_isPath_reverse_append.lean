-- Prove2me | Theorems.Thm_DiracCycle_isPath_reverse_append
-- name    : DiracCycle.isPath_reverse_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:48:29.296718+00:00
-- url     : https://prove2.me/theorems/86b6fdb8-a5b8-4cec-9d30-5c8cbbc43fda
-- title:
--   Dirac Cycle: is Path reverse append
-- statement:
--   Two paths from `x` sharing only `x` give a path between their ends.
--
--   Source: https://github.com/jtraverso/dirac-common-cycle/blob/3c9e9966662cb99c0e4f11d771011bc904dc627f/DiracCycleLib/DiracCycle.lean#L121-L134
-- source:
--   https://github.com/jtraverso/dirac-common-cycle/blob/3c9e9966662cb99c0e4f11d771011bc904dc627f/DiracCycleLib/DiracCycle.lean#L121-L134

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

theorem DiracCycle.isPath_reverse_append {x u v : V} (P₁ : G.Walk x u) (P₂ : G.Walk x v) (h₁ : P₁.IsPath)
    (h₂ : P₂.IsPath) (hdisj : ∀ y ∈ P₁.support, y ∈ P₂.support → y = x) :
    (P₁.reverse.append P₂).IsPath := by sorry
