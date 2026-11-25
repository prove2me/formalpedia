-- Prove2me | Theorems.Thm_Erdos657Proof_pt_apply
-- name    : Erdos657Proof.pt_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:21:50.874257+00:00
-- url     : https://prove2.me/theorems/3429bafd-491f-483e-a089-758dd5132e77
-- title:
--   Erdos657 Proof: pt apply
-- statement:
--   The Erdos657 Proof construction uses the pt apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/veljjanoski/erdos657-palomar/blob/e44e1eb1d4a525f66a7a297235c956a29f56a535/Solution.lean#L77-L78
-- source:
--   https://github.com/veljjanoski/erdos657-palomar/blob/e44e1eb1d4a525f66a7a297235c956a29f56a535/Solution.lean#L77-L78

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

theorem Erdos657Proof.pt_apply {k : ℕ} (S : Finset (Fin k)) (i : Fin k) : pt S i = if i ∈ S then w i else 0 := by sorry
