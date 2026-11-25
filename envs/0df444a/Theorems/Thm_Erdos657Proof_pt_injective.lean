-- Prove2me | Theorems.Thm_Erdos657Proof_pt_injective
-- name    : Erdos657Proof.pt_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:21:52.376829+00:00
-- url     : https://prove2.me/theorems/146e0080-43b7-4d2c-899c-21c1b8d0d8d6
-- title:
--   Erdos657 Proof: pt injective
-- statement:
--   The Erdos657 Proof construction uses the pt injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/veljjanoski/erdos657-palomar/blob/e44e1eb1d4a525f66a7a297235c956a29f56a535/Solution.lean#L111-L115
-- source:
--   https://github.com/veljjanoski/erdos657-palomar/blob/e44e1eb1d4a525f66a7a297235c956a29f56a535/Solution.lean#L111-L115

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

theorem Erdos657Proof.pt_injective (k : ℕ) : Function.Injective (pt (k := k)) := by sorry
