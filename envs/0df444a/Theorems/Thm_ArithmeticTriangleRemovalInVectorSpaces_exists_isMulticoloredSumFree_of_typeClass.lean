-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_exists_isMulticoloredSumFree_of_typeClass
-- name    : ArithmeticTriangleRemovalInVectorSpaces.exists_isMulticoloredSumFree_of_typeClass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:12:04.123963+00:00
-- url     : https://prove2.me/theorems/7d182147-b224-4317-9e4a-26e54d54e7d9
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: exists is Multicolored Sum Free of type Class
-- statement:
--   **The sum-free family of a base point.** If `a₀ r + b₀ r + c₀ r = p - 1` for every `r` and
--   `1 ≤ w` is at most the size of the type classes of `a₀`, `b₀` and `c₀`, then there is a
--   multicolored sum-free family in `Fin n → ZMod p` with at least
--   `w * exp (-4 * √(log ((12 + 2 * p) * p ^ (3 * n)))) / (4 * (12 + 2 * p))` members.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Construction/Family.lean#L186-L221
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Construction/Family.lean#L186-L221

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_TypeClass
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_MulticoloredSumFree_Basic
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_Behrend
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_Hash
public import Mathlib.NumberTheory.Bertrand
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Construction_Family
set_option autoImplicit true
@[expose] public section
public section
open Finset Real
open ArithmeticTriangleRemovalInVectorSpaces
variable {n p : ℕ}
variable {a₀ b₀ c₀ : Fin n → ℕ}

theorem ArithmeticTriangleRemovalInVectorSpaces.exists_isMulticoloredSumFree_of_typeClass (hp : 2 ≤ p)
    (h₀ : ∀ r, a₀ r + b₀ r + c₀ r = p - 1) {w : ℝ} (hw : 1 ≤ w) (hwa : w ≤ #(typeClass a₀))
    (hwb : w ≤ #(typeClass b₀)) (hwc : w ≤ #(typeClass c₀)) :
    ∃ (m : ℕ) (x y z : Fin m → Fin n → ZMod p), IsMulticoloredSumFree x y z ∧
      w * exp (-4 * √(log ((12 + 2 * p) * p ^ (3 * n)))) / (4 * (12 + 2 * p)) ≤ m := by sorry
