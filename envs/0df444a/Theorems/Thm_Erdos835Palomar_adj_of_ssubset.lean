-- Prove2me | Theorems.Thm_Erdos835Palomar_adj_of_ssubset
-- name    : Erdos835Palomar.adj_of_ssubset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:11:54.109795+00:00
-- url     : https://prove2.me/theorems/236ff864-2188-57bf-8904-f3357dead149
-- title:
--   Erdos835 Palomar: adj of ssubset
-- statement:
--   Two different `k`-subsets of a `(k+1)`-set are adjacent in `J(2k, k)`.
--
--   Source: https://github.com/stokes/erdos835-palomar/blob/3a8d4cb348203b172c050917eaf1fa03679f002f/Solution.lean#L214-L231
-- source:
--   https://github.com/stokes/erdos835-palomar/blob/3a8d4cb348203b172c050917eaf1fa03679f002f/Solution.lean#L214-L231

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

theorem Erdos835Palomar.adj_of_ssubset {A : Finset (Fin (2 * k))} (hA : #A = k + 1)
    {s t : {s : Finset (Fin (2 * k)) // #s = k}} (hs : s.val ⊂ A) (ht : t.val ⊂ A)
    (hst : s ≠ t) : J(2 * k, k).Adj s t := by sorry
