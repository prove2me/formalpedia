-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_self_mem_typeClass
-- name    : ArithmeticTriangleRemovalInVectorSpaces.self_mem_typeClass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:35.706911+00:00
-- url     : https://prove2.me/theorems/dd9b7eb3-3dd3-4528-97bb-fe736a74ff67
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: self mem type Class
-- statement:
--   The Arithmetic Triangle Removal In Vector Spaces construction uses the self mem type Class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Construction/TypeClass.lean#L51-L52
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Construction/TypeClass.lean#L51-L52

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

theorem ArithmeticTriangleRemovalInVectorSpaces.self_mem_typeClass (a : Fin n → ℕ) : a ∈ typeClass a := by sorry
