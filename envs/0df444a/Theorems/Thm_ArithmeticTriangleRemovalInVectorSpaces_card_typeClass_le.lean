-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_card_typeClass_le
-- name    : ArithmeticTriangleRemovalInVectorSpaces.card_typeClass_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:46.963902+00:00
-- url     : https://prove2.me/theorems/955350b0-48ae-4fbf-81b5-e319563c8ce9
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: card type Class le
-- statement:
--   The Arithmetic Triangle Removal In Vector Spaces construction uses the card type Class le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Construction/TypeClass.lean#L75-L81
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Construction/TypeClass.lean#L75-L81

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Perm
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_LogSumSupport
public import Mathlib.GroupTheory.Perm.DomMulAct
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_TypeClass
set_option autoImplicit true
@[expose] public section
public section
open Finset Real
open ArithmeticTriangleRemovalInVectorSpaces
variable {n N : ℕ} {a b b' : Fin n → ℕ}

theorem ArithmeticTriangleRemovalInVectorSpaces.card_typeClass_le {p : ℕ} (ha : ∀ r, a r < p) : #(typeClass a) ≤ p ^ n := by sorry
