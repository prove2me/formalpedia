-- Prove2me | Theorems.Thm_Auto_triangularKernelCoefficient_pos
-- name    : Auto.triangularKernelCoefficient_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:29:07.498478+00:00
-- url     : https://prove2.me/theorems/a5a6c201-ee32-438d-8dfe-1ee9e26ebbec
-- title:
--   Auto: triangular Kernel Coefficient pos
-- statement:
--   The Auto construction uses the triangular Kernel Coefficient pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7882-L7884
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7882-L7884

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

theorem Auto.triangularKernelCoefficient_pos : 0 < triangularKernelCoefficient := by sorry
