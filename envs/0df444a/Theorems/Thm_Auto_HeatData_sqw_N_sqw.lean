-- Prove2me | Theorems.Thm_Auto_HeatData_sqw_N_sqw
-- name    : Auto.HeatData.sqw_N_sqw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:28:16.218776+00:00
-- url     : https://prove2.me/theorems/44796791-dafe-42e6-aea3-2fdea3d57deb
-- title:
--   Heat Data: sqw N sqw
-- statement:
--   The Heat Data construction uses the sqw N sqw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3541-L3550
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3541-L3550

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
variable (Hd : HeatData ι) (p σ : Fin 3 → ℝ)

theorem Auto.HeatData.sqw_N_sqw (hh : 0 < Hd.h) {v : Fin 3} (hσ : 0 < σ v) :
    rdiag (Hd.sqw p σ v) * Hd.N p σ v * rdiag (Hd.sqw p σ v) = rdiag (Hd.dw p σ v) := by sorry
