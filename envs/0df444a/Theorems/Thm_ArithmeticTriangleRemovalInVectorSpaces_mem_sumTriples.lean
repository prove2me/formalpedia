-- Prove2me | Theorems.Thm_ArithmeticTriangleRemovalInVectorSpaces_mem_sumTriples
-- name    : ArithmeticTriangleRemovalInVectorSpaces.mem_sumTriples
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:09:01.17393+00:00
-- url     : https://prove2.me/theorems/c4e326e4-b579-432c-8b92-9b285f9d9897
-- title:
--   Arithmetic Triangle Removal In Vector Spaces: mem sum Triples
-- statement:
--   The Arithmetic Triangle Removal In Vector Spaces construction uses the mem sum Triples property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Basic.lean#L52-L54
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/Coupling/Basic.lean#L52-L54

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

theorem ArithmeticTriangleRemovalInVectorSpaces.mem_sumTriples {N a b c : ℕ} : (a, b, c) ∈ sumTriples N ↔ a + b + c = N := by sorry
