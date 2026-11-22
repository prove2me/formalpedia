-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_compatible_of_eq_zero_of_eq_zero
-- name    : ArithmeticTriangleRemovalInVectorSpaces.compatible_of_eq_zero_of_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:12:29.614907+00:00
-- url     : https://prove2.me/theorems/53083b69-ff8d-429c-809f-0484668ab43b
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: compatible of eq zero of eq zero
-- statement:
--   **Corollary 3.2 of Pebody.** If Pebody's theorem holds at level `n`, then decreasing mass
--   functions at level `n + 1` whose second and third members vanish at `n + 1` are compatible.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Peeling.lean#L312-L349
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Peeling.lean#L312-L349

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Peeling
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ArithmeticTriangleRemovalInVectorSpaces
variable {N : ℕ} {π π' π₁ π₂ π₃ : ℕ → ℝ}

theorem ArithmeticTriangleRemovalInVectorSpaces.compatible_of_eq_zero_of_eq_zero {n : ℕ} (ih : DecreasingCompatible n)
    (h₁ : IsDecreasingOn (n + 1) π₁) (h₂ : IsDecreasingOn (n + 1) π₂)
    (h₃ : IsDecreasingOn (n + 1) π₃) (h₂N : π₂ (n + 1) = 0) (h₃N : π₃ (n + 1) = 0)
    (hm₂ : mass (n + 1) π₂ = mass (n + 1) π₁) (hm₃ : mass (n + 1) π₃ = mass (n + 1) π₁)
    (hmom : moment (n + 1) π₁ + moment (n + 1) π₂ + moment (n + 1) π₃ =
      (n + 1 : ℕ) * mass (n + 1) π₁) :
    Compatible (n + 1) π₁ π₂ π₃ := by sorry
