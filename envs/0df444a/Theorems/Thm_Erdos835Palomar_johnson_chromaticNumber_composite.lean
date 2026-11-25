-- Prove2me | Theorems.Thm_Erdos835Palomar_johnson_chromaticNumber_composite
-- name    : Erdos835Palomar.johnson_chromaticNumber_composite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:12:21.436681+00:00
-- url     : https://prove2.me/theorems/50e240be-1250-4d55-adcf-08d0501292d1
-- title:
--   Erdos835 Palomar: johnson chromatic Number composite
-- statement:
--   The Challenge statement `johnson_chromaticNumber_composite` (Ma–Tang, composite case).
--
--   Source: https://github.com/stokes/erdos835-palomar/blob/3a8d4cb348203b172c050917eaf1fa03679f002f/Solution.lean#L290-L294
-- source:
--   https://github.com/stokes/erdos835-palomar/blob/3a8d4cb348203b172c050917eaf1fa03679f002f/Solution.lean#L290-L294

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

theorem Erdos835Palomar.johnson_chromaticNumber_composite (k : ℕ) (hk : 2 < k) (h : Composite (k + 1)) :
    k + 1 < J(2 * k, k).chromaticNumber := by sorry
