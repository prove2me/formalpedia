-- Prove2me | Theorems.Thm_Auto_HeatData_norm_A_le
-- name    : Auto.HeatData.norm_A_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:34:47.005971+00:00
-- url     : https://prove2.me/theorems/92718556-9158-4ac2-b8c6-87d0845645bd
-- title:
--   Heat Data: norm A le
-- statement:
--   The Heat Data construction uses the norm A le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4142-L4149
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4142-L4149

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Auto.HeatData
variable (Hd : HeatData ι)
omit [DecidableEq ι]

theorem Auto.HeatData.norm_A_le (k : Fin 3) (i j : ι) : ‖Hd.A k i j‖ ≤ Hd.MA := by sorry
