-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_sum_eq_of_mem_typeClass
-- name    : ArithmeticTriangleRemovalInVectorSpaces.sum_eq_of_mem_typeClass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:48.416605+00:00
-- url     : https://prove2.me/theorems/fc6aec34-56d6-408e-bef9-961ac29d64c5
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: sum eq of mem type Class
-- statement:
--   The Arithmetic Triangle Removal In Vector Spaces construction uses the sum eq of mem type Class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Construction/TypeClass.lean#L71-L73
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Construction/TypeClass.lean#L71-L73

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

theorem ArithmeticTriangleRemovalInVectorSpaces.sum_eq_of_mem_typeClass (hb : b ∈ typeClass a) : ∑ r, b r = ∑ r, a r := by sorry
