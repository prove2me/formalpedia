-- Prove2me | Theorems.Thm_Auto_triangularCutoffProfile_bound
-- name    : Auto.triangularCutoffProfile_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:56:13.114685+00:00
-- url     : https://prove2.me/theorems/6781eaa2-088b-4ca6-a56a-c87c55448299
-- title:
--   Auto: triangular Cutoff Profile bound
-- statement:
--   The Auto construction uses the triangular Cutoff Profile bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7817-L7823
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7817-L7823

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

theorem Auto.triangularCutoffProfile_bound {u : ℝ} (hu : 0 ≤ u) : |triangularCutoffProfile u| ≤ 3 := by sorry
