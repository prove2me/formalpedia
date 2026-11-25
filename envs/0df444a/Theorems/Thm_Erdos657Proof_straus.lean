-- Prove2me | Theorems.Thm_Erdos657Proof_straus
-- name    : Erdos657Proof.straus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:23:37.234671+00:00
-- url     : https://prove2.me/theorems/faf1c521-8afd-4ae5-a20d-4288c9dfbf99
-- title:
--   Erdos657 Proof: straus
-- statement:
--   The Erdos657 Proof construction uses the straus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/veljjanoski/erdos657-palomar/blob/e44e1eb1d4a525f66a7a297235c956a29f56a535/Solution.lean#L158-L161
-- source:
--   https://github.com/veljjanoski/erdos657-palomar/blob/e44e1eb1d4a525f66a7a297235c956a29f56a535/Solution.lean#L158-L161

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

theorem Erdos657Proof.straus (k : ℕ) :
    ∃ A : Finset (ℝ^k), A.card = 2 ^ k ∧ (A : Set (ℝ^k)).IsIsoscelesFree ∧
      distinctDistances A ≤ 2 ^ k - 1 := by sorry
