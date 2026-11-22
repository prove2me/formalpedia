-- Prove2me | Theorems.Thm_Auto_HeatData_ofReal_costDensity
-- name    : Auto.HeatData.ofReal_costDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:28:47.939704+00:00
-- url     : https://prove2.me/theorems/d91445ff-32fe-4b9d-95ab-0f4d0cec9ab3
-- title:
--   Heat Data: of Real cost Density
-- statement:
--   The Heat Data construction uses the of Real cost Density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6136-L6146
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6136-L6146

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
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Auto.HeatData
variable (Hd : HeatData ι)

theorem Auto.HeatData.ofReal_costDensity {η : ℝ} (hη : 0 < η) (α : Fin 3 → ℝ) (z : ℝ × (Fin 3 → ℝ)) :
    ENNReal.ofReal (Hd.costDensity α η z) = ENNReal.ofReal (Gm (1 / 10) 0 z.1 z.2) * ∑ v,
      matCost (Hd.T z.2 (sig α z.1) v + (η : ℂ) • 1) (Hd.Ui z.2 (sig α z.1) v) := by sorry
