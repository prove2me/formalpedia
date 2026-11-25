-- Prove2me | Theorems.Thm_Erdos835Palomar_color_count
-- name    : Erdos835Palomar.color_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:12:31.630448+00:00
-- url     : https://prove2.me/theorems/35722e04-e3f4-4069-aa0a-1729ee4c852a
-- title:
--   Erdos835 Palomar: color count
-- statement:
--   Double counting: for any colour `i` and `W` with `#W = k + j`, `1 ≤ j`,
--   `(k + 1) * #{k-subsets of W of colour i} = (k + j).choose j`.
--
--   Source: https://github.com/stokes/erdos835-palomar/blob/3a8d4cb348203b172c050917eaf1fa03679f002f/Solution.lean#L164-L198
-- source:
--   https://github.com/stokes/erdos835-palomar/blob/3a8d4cb348203b172c050917eaf1fa03679f002f/Solution.lean#L164-L198

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

theorem Erdos835Palomar.color_count (c : {s : Finset (Fin (2 * k)) // #s = k} → Fin (k + 1))
    (hc : ∀ A : Finset (Fin (2 * k)), #A = k + 1 → image c {s | s.val ⊂ A} = univ)
    (i : Fin (k + 1)) (j : ℕ) (hj : 1 ≤ j) (W : Finset (Fin (2 * k))) (hW : #W = k + j) :
    (k + 1) * #({s | s.val ⊆ W ∧ c s = i} : Finset {s : Finset (Fin (2 * k)) // #s = k}) =
      (k + j).choose j := by sorry
