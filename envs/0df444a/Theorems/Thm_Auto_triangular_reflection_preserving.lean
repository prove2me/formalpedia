-- Prove2me | Theorems.Thm_Auto_triangular_reflection_preserving
-- name    : Auto.triangular_reflection_preserving
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:57:43.196359+00:00
-- url     : https://prove2.me/theorems/2bdc3f08-b5c9-41c2-b2b8-e8f906287bfc
-- title:
--   Auto: triangular reflection preserving
-- statement:
--   Reflection in the singular coordinate preserves volume.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8125-L8128
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8125-L8128

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

theorem Auto.triangular_reflection_preserving :
    MeasurePreserving (fun q : (ℝ × ℝ) × ℝ => (q.1, -q.2)) := by sorry
