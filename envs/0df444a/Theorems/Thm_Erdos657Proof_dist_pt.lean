-- Prove2me | Theorems.Thm_Erdos657Proof_dist_pt
-- name    : Erdos657Proof.dist_pt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:21:38.089571+00:00
-- url     : https://prove2.me/theorems/1b431e75-caa0-49cd-bec8-c4d237f3f37e
-- title:
--   Erdos657 Proof: dist pt
-- statement:
--   The Erdos657 Proof construction uses the dist pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/veljjanoski/erdos657-palomar/blob/e44e1eb1d4a525f66a7a297235c956a29f56a535/Solution.lean#L95-L104
-- source:
--   https://github.com/veljjanoski/erdos657-palomar/blob/e44e1eb1d4a525f66a7a297235c956a29f56a535/Solution.lean#L95-L104

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

theorem Erdos657Proof.dist_pt {k : ℕ} (S T : Finset (Fin k)) :
    dist (pt S) (pt T) = Real.sqrt (g (symmDiff S T)) := by sorry
