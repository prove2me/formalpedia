-- Prove2me | Theorems.Thm_Auto_triangularSpaceEquiv_preserving
-- name    : Auto.triangularSpaceEquiv_preserving
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:26:03.13517+00:00
-- url     : https://prove2.me/theorems/e50c7c10-a57e-41c2-b660-87a71aa10d85
-- title:
--   Auto: triangular Space Equiv preserving
-- statement:
--   The Auto construction uses the triangular Space Equiv preserving property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8311-L8317
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8311-L8317

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

theorem Auto.triangularSpaceEquiv_preserving : MeasurePreserving triangularSpaceEquiv := by sorry
