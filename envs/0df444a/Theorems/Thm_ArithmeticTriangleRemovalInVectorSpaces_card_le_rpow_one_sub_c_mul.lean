-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_card_le_rpow_one_sub_c_mul
-- name    : ArithmeticTriangleRemovalInVectorSpaces.card_le_rpow_one_sub_c_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:15:58.574076+00:00
-- url     : https://prove2.me/theorems/dd50f862-9c7d-4fa5-80f7-b2d846c5729d
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: card le rpow one sub c mul
-- statement:
--   **The Kleinberg–Sawin–Speyer bound** (Theorem 2 of Fox and Lovász). If the triples
--   `(x i, y i, z i)` in `Fin n → ZMod p` satisfy `x i + y j + z k = 0` exactly when `i = j = k`, then
--   there are at most `p ^ ((1 - c p) * n)` of them.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/ZMod.lean#L54-L59
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/ZMod.lean#L54-L59

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Exponent
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_LowerBound
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_MaximalFamily
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_TensorPower
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Product
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_TensorPower
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Tightness_Exponent
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_ZMod
set_option autoImplicit true
@[expose] public section
public section
open Finset Function
open ArithmeticTriangleRemovalInVectorSpaces
variable {p n : ℕ} [Fact p.Prime]

theorem ArithmeticTriangleRemovalInVectorSpaces.card_le_rpow_one_sub_c_mul {ι : Type*} [Fintype ι] {x y z : ι → Fin n → ZMod p}
    (h : ∀ i j k, x i + y j + z k = 0 ↔ i = j ∧ j = k) :
    Fintype.card ι ≤ (p : ℝ) ^ ((1 - c p) * n) := by sorry
