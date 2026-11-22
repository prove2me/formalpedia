-- Prove2me | Theorems.Thm_Auto_HeatData_e_heat_row
-- name    : Auto.HeatData.e_heat_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:46:11.017322+00:00
-- url     : https://prove2.me/theorems/93d16aaa-0871-4ded-b4c5-7eb232cab01c
-- title:
--   Heat Data: e heat row
-- statement:
--   The Heat Data construction uses the e heat row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3289-L3321
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3289-L3321

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

theorem Auto.HeatData.e_heat_row (hh : 0 ≤ Hd.h) {η : ℝ} (hη : 0 < η) (hσ : ∀ k, 0 < σ k) (v : Fin 3) :
    HasDerivAt (fun q => Hd.e (Function.update p v q) σ η v) (tr32 η (Hd.T p σ v) (Hd.Ui p σ v))
      (p v) ∧ HasDerivAt (fun q => tr32 η (Hd.T (Function.update p v q) σ v) (Hd.Ui
      (Function.update p v q) σ v)) (Hd.V p σ η v + tr32 η (Hd.T p σ v) (wGram (Hd.Brow p σ v)
      (Hd.ddw p σ v))) (p v) ∧ HasDerivAt (fun τ => Hd.e p (Function.update σ v τ) η v) (tr32 η
      (Hd.T p σ v) (wGram (Hd.Brow p σ v) (fun i => Hd.ddw p σ v i / 2))) (σ v) := by sorry
