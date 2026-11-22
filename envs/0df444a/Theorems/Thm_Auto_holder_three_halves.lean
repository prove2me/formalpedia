-- Prove2me | Theorems.Thm_Auto_holder_three_halves
-- name    : Auto.holder_three_halves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:36:43.929822+00:00
-- url     : https://prove2.me/theorems/c97cd54d-9c59-4d30-8d3b-5c9d1ffbeeac
-- title:
--   Auto: holder three halves
-- statement:
--   The Auto construction uses the holder three halves property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5628-L5641
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5628-L5641

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section

theorem Auto.holder_three_halves {κ : Type*} (s : Finset κ) (μ a : κ → ℝ) (hμ : ∀ k, 0 ≤ μ k)
    (ha : ∀ k, 0 ≤ a k) :
    (∑ k ∈ s, μ k * a k) ^ (3 / 2 : ℝ) ≤ (∑ k ∈ s, μ k) ^ (1 / 2 : ℝ) * ∑ k ∈ s, μ k * a k ^ (3
      / 2 : ℝ) := by sorry
