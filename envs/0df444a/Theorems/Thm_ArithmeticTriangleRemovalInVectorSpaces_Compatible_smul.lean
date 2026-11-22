-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_Compatible_smul
-- name    : ArithmeticTriangleRemovalInVectorSpaces.Compatible.smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:09:20.449872+00:00
-- url     : https://prove2.me/theorems/ff156507-a7ae-4fa4-b889-2857e6b9de1a
-- title:
--   Compatible: smul
-- statement:
--   The Compatible construction uses the smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Basic.lean#L96-L99
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Basic.lean#L96-L99

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

theorem ArithmeticTriangleRemovalInVectorSpaces.Compatible.smul (h : Compatible N π₁ π₂ π₃) {r : ℝ} (hr : 0 ≤ r) :
    Compatible N (r • π₁) (r • π₂) (r • π₃) := by sorry
