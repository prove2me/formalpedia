-- Prove2me | Theorems.Thm_Erdos835Palomar_not_property_of_not_prime
-- name    : Erdos835Palomar.not_property_of_not_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:12:21.136247+00:00
-- url     : https://prove2.me/theorems/c6b9c0ce-ca3b-447a-b0df-cadc3f8e03f1
-- title:
--   Erdos835 Palomar: not property of not prime
-- statement:
--   Ma–Tang, composite case, for `Property`: if `k + 1` is not prime, `Property k`
--   fails.
--
--   Source: https://github.com/stokes/erdos835-palomar/blob/3a8d4cb348203b172c050917eaf1fa03679f002f/Solution.lean#L202-L211
-- source:
--   https://github.com/stokes/erdos835-palomar/blob/3a8d4cb348203b172c050917eaf1fa03679f002f/Solution.lean#L202-L211

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

theorem Erdos835Palomar.not_property_of_not_prime (k : ℕ) (hk : 2 ≤ k) (hnp : ¬ (k + 1).Prime) :
    ¬ Property k := by sorry
