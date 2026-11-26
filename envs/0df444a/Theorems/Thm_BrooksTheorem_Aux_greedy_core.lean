-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_greedy_core
-- name    : BrooksTheorem.Aux.greedy_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:25:58.257411+00:00
-- url     : https://prove2.me/theorems/9b236d1a-dbca-457f-a337-adc9288d8b10
-- title:
--   Aux: greedy core
-- statement:
--   Greedy colouring along a rank: vertices of larger rank are coloured first.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/Greedy.lean#L51-L165
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/Greedy.lean#L51-L165

module
public import Mathlib
public import Definitions.Def_BrooksLib_Greedy
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*}
variable [Fintype V]

theorem BrooksTheorem.Aux.greedy_core [DecidableEq V] (H : SimpleGraph V) (k : ℕ) (r : V → ℕ) :
    ∀ (n : ℕ) (P : Finset V) (f : V → Fin k), Pᶜ.card = n →
    (∀ u ∈ P, ∀ v ∈ P, H.Adj u v → f u ≠ f v) →
    (∀ w ∉ P, (((nb H w).filter (· ∈ P)).image f).card +
       ((nb H w).filter (fun u => u ∉ P ∧ r w ≤ r u)).card < k) →
    ∃ g : V → Fin k, (∀ v ∈ P, g v = f v) ∧ Proper H g := by sorry
