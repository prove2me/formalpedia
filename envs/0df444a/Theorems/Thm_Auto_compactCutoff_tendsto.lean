-- Prove2me | Theorems.Thm_Auto_compactCutoff_tendsto
-- name    : Auto.compactCutoff_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:55:41.569864+00:00
-- url     : https://prove2.me/theorems/6d18573d-2c9f-4a82-9117-34d150d533a6
-- title:
--   Auto: compact Cutoff tendsto
-- statement:
--   The Auto construction uses the compact Cutoff tendsto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7653-L7658
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7653-L7658

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

theorem Auto.compactCutoff_tendsto (p : ℝ × ℝ) :
    Tendsto (fun n => compactCutoff n p) atTop (𝓝 1) := by sorry
