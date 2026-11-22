-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_le_rpow_C_sub_of_forall_exists_subset
-- name    : ArithmeticTriangleRemovalInVectorSpaces.le_rpow_C_sub_of_forall_exists_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:16:16.841053+00:00
-- url     : https://prove2.me/theorems/b9fce447-b3e7-4c39-9eaf-32828d58a171
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: le rpow C sub of forall exists subset
-- statement:
--   **Asymptotic tightness of the arithmetic triangle removal lemma** (the "Furthermore" part of
--   Theorem 1 of Fox and Lovász). For every `η > 0` and every `0 < ε < ε₀ p η`, any `δ` that works
--   with `ε` in the removal lemma in `Fin n → ZMod p` for every `n` satisfies `δ ≤ ε ^ (C p - η)`.
--   Here `ε₀ p η = p ^ (-(n₀ p η' + 1))` with `η' = c p * min (1 - c p) (c p * η / 2) / 2` and
--   `n₀ p η' = ⌈(2 ^ (p + 3) * p ^ 10 / η') ^ 2⌉ + p ^ 4 + 1`. The proof combines the construction of
--   Section 3 with the multicolored sum-free families of size `p ^ ((1 - c p - η') * n)` of Kleinberg,
--   Sawin and Speyer.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/ZMod.lean#L187-L204
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/ZMod.lean#L187-L204

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
variable {l : ℕ} {ι : Type*} [Fintype ι] {x y z : ι → Fin n → ZMod p}

theorem ArithmeticTriangleRemovalInVectorSpaces.le_rpow_C_sub_of_forall_exists_subset {η ε δ : ℝ} (hη : 0 < η) (hε : 0 < ε)
    (hε₀ : ε < ε₀ p η)
    (hδ : ∀ n (X Y Z : Finset (Fin n → ZMod p)),
      #((X ×ˢ Y ×ˢ Z).filter fun (x, y, z) ↦ x + y + z = 0) < δ * (p ^ n) ^ 2 →
        ∃ X' ⊆ X, ∃ Y' ⊆ Y, ∃ Z' ⊆ Z, #(X \ X') + #(Y \ Y') + #(Z \ Z') ≤ ε * p ^ n ∧
          ∀ x ∈ X', ∀ y ∈ Y', ∀ z ∈ Z', x + y + z ≠ 0) :
    δ ≤ ε ^ (C p - η) := by sorry
