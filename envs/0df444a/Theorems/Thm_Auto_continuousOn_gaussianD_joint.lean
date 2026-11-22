-- Prove2me | Theorems.Thm_Auto_continuousOn_gaussianD_joint
-- name    : Auto.continuousOn_gaussianD_joint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:28:32.033846+00:00
-- url     : https://prove2.me/theorems/33700a8f-f2dc-46dd-9c55-05e71175ce95
-- title:
--   Auto: continuous On gaussian D joint
-- statement:
--   The Auto construction uses the continuous On gaussian D joint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4557-L4567
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4557-L4567

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

theorem Auto.continuousOn_gaussianD_joint (j : ℕ) :
    ContinuousOn (fun z : ℝ × ℝ => gaussianD j z.1 z.2) {z | 0 < z.1} := by sorry
