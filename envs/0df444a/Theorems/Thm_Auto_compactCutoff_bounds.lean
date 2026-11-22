-- Prove2me | Theorems.Thm_Auto_compactCutoff_bounds
-- name    : Auto.compactCutoff_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:55:41.731939+00:00
-- url     : https://prove2.me/theorems/e6303dcf-2575-489e-affd-0222ed0d4e7f
-- title:
--   Auto: compact Cutoff bounds
-- statement:
--   The Auto construction uses the compact Cutoff bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7637-L7639
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7637-L7639

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
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped ENNReal NNReal
open MeasureTheory Filter Topology Real
public section
open Auto
open MeasureTheory Filter Topology Matrix Real
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section

theorem Auto.compactCutoff_bounds (n : ℕ) (p : ℝ × ℝ) :
    0 ≤ compactCutoff n p ∧ compactCutoff n p ≤ 1 := by sorry
