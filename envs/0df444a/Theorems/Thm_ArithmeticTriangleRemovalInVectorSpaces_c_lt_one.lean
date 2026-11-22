-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_c_lt_one
-- name    : ArithmeticTriangleRemovalInVectorSpaces.c_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:09:23.681525+00:00
-- url     : https://prove2.me/theorems/3b5456f9-60ac-43d9-aa3b-cf4909be135d
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: c lt one
-- statement:
--   The exponent `c p` is less than one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/Exponent.lean#L160-L164
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/Exponent.lean#L160-L164

module
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Exponent
set_option autoImplicit true
@[expose] public section
public section
open Finset Filter Topology
open ArithmeticTriangleRemovalInVectorSpaces
variable {p : ℕ}

theorem ArithmeticTriangleRemovalInVectorSpaces.c_lt_one (hp : 2 ≤ p) : c p < 1 := by sorry
