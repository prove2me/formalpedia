-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_IsDecreasingOn_shift
-- name    : ArithmeticTriangleRemovalInVectorSpaces.IsDecreasingOn.shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:59.648153+00:00
-- url     : https://prove2.me/theorems/e8aa874f-1ca0-4c13-921e-36d1659e5cb4
-- title:
--   Is Decreasing On: shift
-- statement:
--   The first mass function after peeling: `π` shifted down by one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Peeling.lean#L135-L138
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Peeling.lean#L135-L138

module
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Peeling
public import Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_Compatible_shift

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ArithmeticTriangleRemovalInVectorSpaces
variable {N : ℕ} {π π' π₁ π₂ π₃ : ℕ → ℝ}

theorem ArithmeticTriangleRemovalInVectorSpaces.IsDecreasingOn.shift (h : IsDecreasingOn (N + 1) π) :
    IsDecreasingOn N fun k ↦ π (k + 1) := by sorry
