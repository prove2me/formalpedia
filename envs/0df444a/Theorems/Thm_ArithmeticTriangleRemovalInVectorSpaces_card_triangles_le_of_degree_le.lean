-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_card_triangles_le_of_degree_le
-- name    : ArithmeticTriangleRemovalInVectorSpaces.card_triangles_le_of_degree_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:23.297809+00:00
-- url     : https://prove2.me/theorems/e81974c8-2687-4179-8d86-d9282ccdc97c
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: card triangles le of degree le
-- statement:
--   **Lemma 5 of Fox and Lovász.** Let `X`, `Y` and `Z` be sets in a finite vector space `V` over
--   `ZMod p` such that the first two vertices of each triangle are linearly independent and their span
--   contains the first two vertices of no other triangle. If every vertex lies in at most `ρ * #V`
--   triangles, then there are at most `125 * p ^ 2 * ρ ^ (1 + c p) * #V ^ 2` triangles.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/DisjointTriangles/Sampling.lean#L474-L498
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/DisjointTriangles/Sampling.lean#L474-L498

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Exponent
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Triangle_Basic
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_LinearMap_Card
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_TensorPower
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_DisjointTriangles_Sampling
set_option autoImplicit true
@[expose] public section
public section
open Finset Module Submodule
open ArithmeticTriangleRemovalInVectorSpaces
variable {p : ℕ} [Fact p.Prime] {V W ι : Type*} [AddCommGroup V] [Module (ZMod p) V] [Fintype V]
  [DecidableEq V] [AddCommGroup W] [Module (ZMod p) W] [Fintype W] [DecidableEq W]
  {X Y Z : Finset V} {x y z x' y' z' : V}

theorem ArithmeticTriangleRemovalInVectorSpaces.card_triangles_le_of_degree_le {ρ : ℝ}
    (hli : ∀ x y z, (x, y, z) ∈ triangles X Y Z → LinearIndependent (ZMod p) ![x, y])
    (hspan : ∀ x y z, (x, y, z) ∈ triangles X Y Z → ∀ x' y' z', (x', y', z') ∈ triangles X Y Z →
      x' ∈ span (ZMod p) {x, y} → y' ∈ span (ZMod p) {x, y} → x' = x ∧ y' = y)
    (hX : ∀ v, #((triangles X Y Z).filter fun (x, _, _) ↦ x = v) ≤ ρ * Fintype.card V)
    (hY : ∀ v, #((triangles X Y Z).filter fun (_, y, _) ↦ y = v) ≤ ρ * Fintype.card V)
    (hZ : ∀ v, #((triangles X Y Z).filter fun (_, _, z) ↦ z = v) ≤ ρ * Fintype.card V) :
    #(triangles X Y Z) ≤ 125 * p ^ 2 * ρ ^ (1 + c p) * Fintype.card V ^ 2 := by sorry
