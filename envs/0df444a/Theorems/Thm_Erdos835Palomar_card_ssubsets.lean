-- Prove2me | Theorems.Thm_Erdos835Palomar_card_ssubsets
-- name    : Erdos835Palomar.card_ssubsets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:11:52.788173+00:00
-- url     : https://prove2.me/theorems/e529c1cf-65fd-57f1-93f6-f368700aeb76
-- title:
--   Erdos835 Palomar: card ssubsets
-- statement:
--   The `k`-subsets strictly inside a `(k+1)`-set: there are `k + 1` of them.
--
--   Source: https://github.com/stokes/erdos835-palomar/blob/3a8d4cb348203b172c050917eaf1fa03679f002f/Solution.lean#L120-L137
-- source:
--   https://github.com/stokes/erdos835-palomar/blob/3a8d4cb348203b172c050917eaf1fa03679f002f/Solution.lean#L120-L137

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib
public import Definitions.Def_Erdos835Palomar_Solution
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open Erdos835Palomar
variable {α : Type*} [DecidableEq α]
variable {k : ℕ}

theorem Erdos835Palomar.card_ssubsets {A : Finset (Fin (2 * k))} (hA : #A = k + 1) :
    #({s | s.val ⊂ A} : Finset {s : Finset (Fin (2 * k)) // #s = k}) = k + 1 := by sorry
