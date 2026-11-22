-- Prove2me | Theorems.Thm_Auto_HeatData_energy_le_W
-- name    : Auto.HeatData.energy_le_W
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:52:07.512051+00:00
-- url     : https://prove2.me/theorems/30885e11-68ce-4911-b21f-dbac775d69cf
-- title:
--   Heat Data: energy le W
-- statement:
--   The Heat Data construction uses the energy le W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5702-L5716
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5702-L5716

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

theorem Auto.HeatData.energy_le_W (p σ : Fin 3 → ℝ) (v : Fin 3) :
    Hd.e p σ 0 v ≤ √2 * (hsSq (Hd.W p σ v) ^ (3 / 2 : ℝ) + hsSq (Hd.W p σ (v - 1)) ^ (3 / 2 :
      ℝ)) := by sorry
