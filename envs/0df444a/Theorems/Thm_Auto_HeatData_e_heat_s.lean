-- Prove2me | Theorems.Thm_Auto_HeatData_e_heat_s
-- name    : Auto.HeatData.e_heat_s
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:47:46.816115+00:00
-- url     : https://prove2.me/theorems/16d80a4b-fd81-47ae-817a-dd0d68580489
-- title:
--   Heat Data: e heat s
-- statement:
--   The Heat Data construction uses the e heat s property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3822-L3835
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3822-L3835

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

theorem Auto.HeatData.e_heat_s (hh : 0 < Hd.h) {η : ℝ} (hη : 0 < η) {α : Fin 3 → ℝ} (hα : ∀ k, 0 < α k)
    {s : ℝ} (hs : 0 < s) (v : Fin 3) :
    HasDerivAt (fun t => Hd.e p (fun k => α k * t) η v) ((α v * tr32 η (Hd.T p (fun k => α k *
      s) v) (wGram (Hd.Brow p (fun k => α k * s) v) (Hd.ddw p (fun k => α k * s) v)) + α (v + 1) *
      tr32 η (Hd.S p (fun k => α k * s) v) (wGram (Hd.Bnext p (fun k => α k * s) v) (Hd.ddw p (fun
      k => α k * s) (v + 1))) + α (v - 1) * tr32 η (Hd.S p (fun k => α k * s) v) (wGram (Hd.Bprev
      p (fun k => α k * s) v) (Hd.ddw p (fun k => α k * s) (v - 1)))) / 2) s := by sorry
