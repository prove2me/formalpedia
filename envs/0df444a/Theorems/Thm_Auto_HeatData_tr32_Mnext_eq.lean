-- Prove2me | Theorems.Thm_Auto_HeatData_tr32_Mnext_eq
-- name    : Auto.HeatData.tr32_Mnext_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:47:27.247803+00:00
-- url     : https://prove2.me/theorems/3601bfb4-c495-44d2-8676-891ab2911969
-- title:
--   Heat Data: tr32 Mnext eq
-- statement:
--   The Heat Data construction uses the tr32 Mnext eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3794-L3803
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3794-L3803

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

theorem Auto.HeatData.tr32_Mnext_eq (hh : 0 < Hd.h) {η : ℝ} (hη : 0 < η) (hσ : ∀ k, 0 < σ k) (v : Fin 3) :
    tr32 η (Hd.T p σ v) (Hd.Mnext p σ v) = tr32 η (Hd.S p σ v) (wGram (Hd.Bnext p σ v) (fun i =>
      Hd.ddw p σ (v + 1) i / 2)) := by sorry
