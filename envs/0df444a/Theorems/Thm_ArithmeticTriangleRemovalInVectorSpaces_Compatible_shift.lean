-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_Compatible_shift
-- name    : ArithmeticTriangleRemovalInVectorSpaces.Compatible.shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:09:21.816182+00:00
-- url     : https://prove2.me/theorems/c08d3c36-4356-4c8d-96d1-43af77d2ebb2
-- title:
--   Compatible: shift
-- statement:
--   Adding `d` to the third variable raises the level by `d`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Basic.lean#L143-L168
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Basic.lean#L143-L168

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Coupling_Basic
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ArithmeticTriangleRemovalInVectorSpaces
variable {N : ℕ} {J J' : ℕ × ℕ × ℕ → ℝ} {g : ℕ × ℕ × ℕ → ℕ} {π₁ π₂ π₃ π₁' π₂' π₃' : ℕ → ℝ}

theorem ArithmeticTriangleRemovalInVectorSpaces.Compatible.shift (h : Compatible N π₁ π₂ π₃) (d : ℕ) :
    Compatible (N + d) π₁ π₂ fun c ↦ if d ≤ c then π₃ (c - d) else 0 := by sorry
