-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_marginal_smul
-- name    : ArithmeticTriangleRemovalInVectorSpaces.marginal_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:32.256799+00:00
-- url     : https://prove2.me/theorems/c032c18c-9115-4e0a-b73d-4560ff71eb8f
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: marginal smul
-- statement:
--   The Arithmetic Triangle Removal In Vector Spaces construction uses the marginal smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Basic.lean#L72-L74
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Basic.lean#L72-L74

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

theorem ArithmeticTriangleRemovalInVectorSpaces.marginal_smul (r : ℝ) : marginal N (r • J) g = r • marginal N J g := by sorry
