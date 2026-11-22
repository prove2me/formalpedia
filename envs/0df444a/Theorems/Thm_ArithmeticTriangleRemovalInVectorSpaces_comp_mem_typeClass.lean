-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_comp_mem_typeClass
-- name    : ArithmeticTriangleRemovalInVectorSpaces.comp_mem_typeClass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:26.773964+00:00
-- url     : https://prove2.me/theorems/ee44f7a6-1e73-44f0-830a-2e650ded8679
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: comp mem type Class
-- statement:
--   The Arithmetic Triangle Removal In Vector Spaces construction uses the comp mem type Class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Construction/TypeClass.lean#L58-L61
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Construction/TypeClass.lean#L58-L61

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

theorem ArithmeticTriangleRemovalInVectorSpaces.comp_mem_typeClass (hb : b ∈ typeClass a) (σ : Equiv.Perm (Fin n)) :
    b ∘ σ ∈ typeClass a := by sorry
