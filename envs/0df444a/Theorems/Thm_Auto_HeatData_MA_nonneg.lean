-- Prove2me | Theorems.Thm_Auto_HeatData_MA_nonneg
-- name    : Auto.HeatData.MA_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:48:34.356622+00:00
-- url     : https://prove2.me/theorems/619aed9b-3e56-45ff-ab63-1b681c77f773
-- title:
--   Heat Data: MA nonneg
-- statement:
--   The Heat Data construction uses the MA nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4152-L4152
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4152-L4152

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

theorem Auto.HeatData.MA_nonneg : 0 ≤ Hd.MA := by sorry
