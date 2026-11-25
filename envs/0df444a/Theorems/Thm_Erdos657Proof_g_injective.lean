-- Prove2me | Theorems.Thm_Erdos657Proof_g_injective
-- name    : Erdos657Proof.g_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:21:44.971693+00:00
-- url     : https://prove2.me/theorems/a7ca6e5a-095f-4444-868f-10c9db2a1bde
-- title:
--   Erdos657 Proof: g injective
-- statement:
--   Binary expansions are unique.
--
--   Source: https://github.com/veljjanoski/erdos657-palomar/blob/e44e1eb1d4a525f66a7a297235c956a29f56a535/Solution.lean#L87-L93
-- source:
--   https://github.com/veljjanoski/erdos657-palomar/blob/e44e1eb1d4a525f66a7a297235c956a29f56a535/Solution.lean#L87-L93

module
public import Mathlib
public import Definitions.Def_Erdos657Palomar_Solution
set_option autoImplicit true
@[expose] public section
public section
open scoped Finset
open Filter
open scoped EuclideanGeometry
open Erdos657Proof
open Finset

theorem Erdos657Proof.g_injective (k : ℕ) : Function.Injective (g (k := k)) := by sorry
