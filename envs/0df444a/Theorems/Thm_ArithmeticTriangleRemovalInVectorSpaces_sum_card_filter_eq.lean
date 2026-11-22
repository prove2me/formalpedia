-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_sum_card_filter_eq
-- name    : ArithmeticTriangleRemovalInVectorSpaces.sum_card_filter_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:41.823812+00:00
-- url     : https://prove2.me/theorems/6688e5c6-d45e-42fc-8c60-2f1fc061c158
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: sum card filter eq
-- statement:
--   The values `k ≤ N` of `a` appear `n` times in total.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Construction/TypeClass.lean#L84-L86
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Construction/TypeClass.lean#L84-L86

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

theorem ArithmeticTriangleRemovalInVectorSpaces.sum_card_filter_eq (ha : ∀ r, a r ≤ N) : ∑ k ∈ range (N + 1), #{r | a r = k} = n := by sorry
