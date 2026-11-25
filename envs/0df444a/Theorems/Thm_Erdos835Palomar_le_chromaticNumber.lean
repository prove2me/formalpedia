-- Prove2me | Theorems.Thm_Erdos835Palomar_le_chromaticNumber
-- name    : Erdos835Palomar.le_chromaticNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:12:07.616798+00:00
-- url     : https://prove2.me/theorems/3f1e3c90-743b-4353-a4f0-9f9b7f262851
-- title:
--   Erdos835 Palomar: le chromatic Number
-- statement:
--   `J(2k, k)` contains a `(k+1)`-clique, so `k + 1 ≤ χ(J(2k, k))` for `k > 0`.
--
--   Source: https://github.com/stokes/erdos835-palomar/blob/3a8d4cb348203b172c050917eaf1fa03679f002f/Solution.lean#L263-L273
-- source:
--   https://github.com/stokes/erdos835-palomar/blob/3a8d4cb348203b172c050917eaf1fa03679f002f/Solution.lean#L263-L273

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

theorem Erdos835Palomar.le_chromaticNumber (hk : 0 < k) : (k + 1 : ℕ∞) ≤ J(2 * k, k).chromaticNumber := by sorry
