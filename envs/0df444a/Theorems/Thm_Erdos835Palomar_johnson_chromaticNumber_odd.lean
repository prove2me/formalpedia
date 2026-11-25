-- Prove2me | Theorems.Thm_Erdos835Palomar_johnson_chromaticNumber_odd
-- name    : Erdos835Palomar.johnson_chromaticNumber_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:16:15.775902+00:00
-- url     : https://prove2.me/theorems/56756742-35e3-4c2e-bb8b-7f19d23f9e11
-- title:
--   Erdos835 Palomar: johnson chromatic Number odd
-- statement:
--   Odd `k > 2`: then `2 ∣ k + 1` and `2 < k + 1`, so `k + 1` is composite (the same reduction as
--   `Erdos835.johnsonGraph_chromaticNumber_odd_of_johnson_chromaticNumber_composite` in formal-conjectures).
--
--   Source: https://github.com/stokes/erdos835-palomar/blob/3a8d4cb348203b172c050917eaf1fa03679f002f/Solution.lean#L298-L305
-- source:
--   https://github.com/stokes/erdos835-palomar/blob/3a8d4cb348203b172c050917eaf1fa03679f002f/Solution.lean#L298-L305

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

theorem Erdos835Palomar.johnson_chromaticNumber_odd (k : ℕ) (hk : 2 < k) (h : Odd k) :
    k + 1 < J(2 * k, k).chromaticNumber := by sorry
