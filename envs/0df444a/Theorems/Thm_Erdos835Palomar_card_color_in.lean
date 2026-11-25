-- Prove2me | Theorems.Thm_Erdos835Palomar_card_color_in
-- name    : Erdos835Palomar.card_color_in
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:12:29.143301+00:00
-- url     : https://prove2.me/theorems/209a71fd-1349-4ff3-8ff0-71db8b19e2e3
-- title:
--   Erdos835 Palomar: card color in
-- statement:
--   In a `Property k` colouring, each `(k+1)`-set has exactly one `k`-subset of each colour.
--
--   Source: https://github.com/stokes/erdos835-palomar/blob/3a8d4cb348203b172c050917eaf1fa03679f002f/Solution.lean#L140-L160
-- source:
--   https://github.com/stokes/erdos835-palomar/blob/3a8d4cb348203b172c050917eaf1fa03679f002f/Solution.lean#L140-L160

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

theorem Erdos835Palomar.card_color_in (c : {s : Finset (Fin (2 * k)) // #s = k} → Fin (k + 1))
    (hc : ∀ A : Finset (Fin (2 * k)), #A = k + 1 → image c {s | s.val ⊂ A} = univ)
    (A : Finset (Fin (2 * k))) (hA : #A = k + 1) (i : Fin (k + 1)) :
    #({s | s.val ⊂ A ∧ c s = i} : Finset {s : Finset (Fin (2 * k)) // #s = k}) = 1 := by sorry
