-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_compatible_layer
-- name    : ArithmeticTriangleRemovalInVectorSpaces.compatible_layer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:37.457774+00:00
-- url     : https://prove2.me/theorems/560f9028-c4b0-46e8-b97f-0aeae4e37499
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: compatible layer
-- statement:
--   The triples `(0, b, N - b)` with weights `f b`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Basic.lean#L171-L230
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Basic.lean#L171-L230

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

theorem ArithmeticTriangleRemovalInVectorSpaces.compatible_layer {f : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k) :
    Compatible N (fun a ↦ if a = 0 then ∑ k ∈ range (N + 1), f k else 0)
      (fun b ↦ if b ≤ N then f b else 0) fun c ↦ if c ≤ N then f (N - c) else 0 := by sorry
