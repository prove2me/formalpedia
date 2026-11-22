-- Prove2me | Theorems.Thm_Auto_HeatData_phi_le_two
-- name    : Auto.HeatData.phi_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:35:26.819131+00:00
-- url     : https://prove2.me/theorems/942859ab-f6e1-47de-963a-75f0ed9e0a69
-- title:
--   Heat Data: phi le two
-- statement:
--   The Heat Data construction uses the phi le two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4438-L4446
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L4438-L4446

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
omit [Fintype ι] [DecidableEq ι]

theorem Auto.HeatData.phi_le_two {b : ℝ} (hb : 0 < b) (v : Fin 3) (p : Fin 3 → ℝ) : phi b v p ≤ 2 := by sorry
