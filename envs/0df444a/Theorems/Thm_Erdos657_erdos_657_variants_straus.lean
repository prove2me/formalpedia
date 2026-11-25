-- Prove2me | Theorems.Thm_Erdos657_erdos_657_variants_straus
-- name    : Erdos657.erdos_657.variants.straus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:23:56.709913+00:00
-- url     : https://prove2.me/theorems/b5f98577-e981-5313-a052-a62120f2669e
-- title:
--   variants: straus
-- statement:
--   The variants construction uses the straus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/veljjanoski/erdos657-palomar/blob/e44e1eb1d4a525f66a7a297235c956a29f56a535/Solution.lean#L167-L170
-- source:
--   https://github.com/veljjanoski/erdos657-palomar/blob/e44e1eb1d4a525f66a7a297235c956a29f56a535/Solution.lean#L167-L170

module
public import Mathlib
public import Definitions.Def_Erdos657Palomar_Solution
set_option autoImplicit true
@[expose] public section
public section
open scoped Finset
open Filter
open scoped EuclideanGeometry
open Erdos657

theorem Erdos657.erdos_657.variants.straus (k : ℕ) :
    ∃ A : Finset (ℝ^k), A.card = 2 ^ k ∧ (A : Set (ℝ^k)).IsIsoscelesFree ∧
      distinctDistances A ≤ 2 ^ k - 1 := by sorry
