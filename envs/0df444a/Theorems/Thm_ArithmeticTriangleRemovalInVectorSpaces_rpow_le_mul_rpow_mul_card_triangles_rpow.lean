-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_rpow_le_mul_rpow_mul_card_triangles_rpow
-- name    : ArithmeticTriangleRemovalInVectorSpaces.rpow_le_mul_rpow_mul_card_triangles_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:26.62575+00:00
-- url     : https://prove2.me/theorems/eb20ef49-43d4-48e5-af07-9a49e0f3ddd0
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: rpow le mul rpow mul card triangles rpow
-- statement:
--   **Pruning.** If the first two vertices of each triangle of `X × Y × Z` are linearly
--   independent, their span contains the first two vertices of no other triangle, and `X × Y × Z`
--   contains `m` vertex-disjoint triangles `(x i, y i, z i)`, then
--   `(η * m / 2) ^ (1 + c p) ≤ 125 * p ^ 2 * #V ^ (1 - c p) * D ^ c p`, where `η = c p / (1 + c p)`
--   and `D` is the number of triangles.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/DisjointTriangles/Pruning.lean#L233-L272
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/DisjointTriangles/Pruning.lean#L233-L272

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Exponent
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Triangle_Basic
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_Sampling
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_Pruning
set_option autoImplicit true
@[expose] public section
public section
open Finset Function Submodule
open ArithmeticTriangleRemovalInVectorSpaces
variable {V ι : Type*} [AddCommGroup V] [DecidableEq V] [Fintype ι] {x y z : ι → V}
variable {A η : ℝ} {X Y Z X' Y' Z' : Finset V} {v : V}
variable {p : ℕ} [Fact p.Prime] [Module (ZMod p) V] [Fintype V]

theorem ArithmeticTriangleRemovalInVectorSpaces.rpow_le_mul_rpow_mul_card_triangles_rpow
    (hli : ∀ x y z, (x, y, z) ∈ triangles X Y Z → LinearIndependent (ZMod p) ![x, y])
    (hspan : ∀ x y z, (x, y, z) ∈ triangles X Y Z → ∀ x' y' z', (x', y', z') ∈ triangles X Y Z →
      x' ∈ span (ZMod p) {x, y} → y' ∈ span (ZMod p) {x, y} → x' = x ∧ y' = y)
    (hx : Injective x) (hy : Injective y) (hz : Injective z) (hxX : ∀ i, x i ∈ X)
    (hyY : ∀ i, y i ∈ Y) (hzZ : ∀ i, z i ∈ Z) (hsum : ∀ i, x i + y i + z i = 0) :
    (c p / (1 + c p) * Fintype.card ι / 2) ^ (1 + c p) ≤
      125 * p ^ 2 * Fintype.card V ^ (1 - c p) * #(triangles X Y Z) ^ c p := by sorry
