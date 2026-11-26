-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_greedy_reach
-- name    : BrooksTheorem.Aux.greedy_reach
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:25:50.344781+00:00
-- url     : https://prove2.me/theorems/cdaecac7-b3b7-45a9-9f60-08a60a783728
-- title:
--   Aux: greedy reach
-- statement:
--   Greedy colouring towards terminals: if every uncoloured vertex reaches a terminal avoiding
--   the precoloured set, and terminals have fewer than `k` constraints, the colouring extends.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/Greedy.lean#L174-L216
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/Greedy.lean#L174-L216

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

theorem BrooksTheorem.Aux.greedy_reach [DecidableEq V] (H : SimpleGraph V) (k : ℕ) (hdeg : ∀ v, (nb H v).card ≤ k)
    (P : Finset V) (f : V → Fin k)
    (hf : ∀ u ∈ P, ∀ v ∈ P, H.Adj u v → f u ≠ f v) (T : V → Prop)
    (hT : ∀ w ∉ P, T w → (((nb H w).filter (· ∈ P)).image f).card +
       ((nb H w).filter (· ∉ P)).card < k)
    (hreach : ∀ w ∉ P, ∃ n, near H P T n w) :
    ∃ g : V → Fin k, (∀ v ∈ P, g v = f v) ∧ Proper H g := by sorry
