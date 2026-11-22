-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsDecreasingOn_eq_hat
-- name    : ArithmeticTriangleRemovalInVectorSpaces.IsDecreasingOn.eq_hat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:12:50.378805+00:00
-- url     : https://prove2.me/theorems/d00e9d13-2638-4e01-86c2-8a7b158902ca
-- title:
--   Is Decreasing On: eq hat
-- statement:
--   **A decreasing mass function is a combination of uniform distributions**, with the nonnegative
--   weights `(k + 1) * (π k - π (k + 1))`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Uniform.lean#L172-L189
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Uniform.lean#L172-L189

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Peeling
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Uniform
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ArithmeticTriangleRemovalInVectorSpaces
variable {N k : ℕ} {π π' π₁ π₂ π₃ : ℕ → ℝ}

theorem ArithmeticTriangleRemovalInVectorSpaces.IsDecreasingOn.eq_hat (h : IsDecreasingOn N π) :
    π = hat N fun k ↦ (k + 1) * (π k - π (k + 1)) := by sorry
