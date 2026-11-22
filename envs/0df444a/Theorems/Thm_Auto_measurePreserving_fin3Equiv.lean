-- Prove2me | Theorems.Thm_Auto_measurePreserving_fin3Equiv
-- name    : Auto.measurePreserving_fin3Equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:38:11.222814+00:00
-- url     : https://prove2.me/theorems/8b7d057b-e2ac-4621-b691-d9628c8e10d2
-- title:
--   Auto: measure Preserving fin3 Equiv
-- statement:
--   The Auto construction uses the measure Preserving fin3 Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8385-L8391
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8385-L8391

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

theorem Auto.measurePreserving_fin3Equiv :
    MeasurePreserving fin3Equiv volume ((volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ)) := by sorry
