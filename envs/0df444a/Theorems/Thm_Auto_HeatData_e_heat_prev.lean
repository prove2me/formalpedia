-- Prove2me | Theorems.Thm_Auto_HeatData_e_heat_prev
-- name    : Auto.HeatData.e_heat_prev
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:33:56.746221+00:00
-- url     : https://prove2.me/theorems/6daae14c-1a69-449a-80c6-e16795e1d386
-- title:
--   Heat Data: e heat prev
-- statement:
--   The Heat Data construction uses the e heat prev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3368-L3405
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3368-L3405

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

theorem Auto.HeatData.e_heat_prev (hh : 0 ≤ Hd.h) {η : ℝ} (hη : 0 < η) (hσ : ∀ k, 0 < σ k) (v : Fin 3) :
    HasDerivAt (fun q => Hd.e (Function.update p (v - 1) q) σ η v) (tr32 η (Hd.S p σ v)
      (Hd.Pprev p σ v)) (p (v - 1)) ∧ HasDerivAt (fun q => tr32 η (Hd.S (Function.update p (v - 1)
      q) σ v) (Hd.Pprev (Function.update p (v - 1) q) σ v)) (Hd.Yprev p σ η v + tr32 η (Hd.S p σ
      v) (wGram (Hd.Bprev p σ v) (Hd.ddw p σ (v - 1)))) (p (v - 1)) ∧ HasDerivAt (fun τ => Hd.e p
      (Function.update σ (v - 1) τ) η v) (tr32 η (Hd.S p σ v) (wGram (Hd.Bprev p σ v) (fun i =>
      Hd.ddw p σ (v - 1) i / 2))) (σ (v - 1)) := by sorry
