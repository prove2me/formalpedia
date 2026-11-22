-- Prove2me | Theorems.Thm_Auto_HeatData_norm_rowMat_le
-- name    : Auto.HeatData.norm_rowMat_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:48:45.519519+00:00
-- url     : https://prove2.me/theorems/a1c7a7be-1137-4547-bc77-b62b3605d077
-- title:
--   Heat Data: norm row Mat le
-- statement:
--   The Heat Data construction uses the norm row Mat le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4155-L4159
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4155-L4159

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

theorem Auto.HeatData.norm_rowMat_le (v : Fin 3) (i : ι) (a : ι ⊕ ι) :
    ‖rowMat (Hd.A v) (Hd.A (v - 1)) i a‖ ≤ Hd.MA := by sorry
