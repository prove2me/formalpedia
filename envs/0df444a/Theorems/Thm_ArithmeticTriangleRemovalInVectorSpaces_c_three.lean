-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_c_three
-- name    : ArithmeticTriangleRemovalInVectorSpaces.c_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:15:53.725644+00:00
-- url     : https://prove2.me/theorems/117aead5-fcb0-47d3-b924-468822dae4ac
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: c three
-- statement:
--   With `a = (√33 - 1) / 8` and `b = a ^ (-2 / 3) + a ^ (1 / 3) + a ^ (4 / 3)`, the exponent
--   `c 3` is `1 - log b / log 3`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/SmallPrimes.lean#L100-L115
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/MulticoloredSumFree/SmallPrimes.lean#L100-L115

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Exponent
public import Mathlib.Analysis.MeanInequalities
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_SmallPrimes
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ArithmeticTriangleRemovalInVectorSpaces

theorem ArithmeticTriangleRemovalInVectorSpaces.c_three {a : ℝ} (ha : a = (√33 - 1) / 8) :
    c 3 = 1 - Real.log (a ^ (-2 / 3 : ℝ) + a ^ (1 / 3 : ℝ) + a ^ (4 / 3 : ℝ)) / Real.log 3 := by sorry
