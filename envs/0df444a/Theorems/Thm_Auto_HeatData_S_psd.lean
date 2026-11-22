-- Prove2me | Theorems.Thm_Auto_HeatData_S_psd
-- name    : Auto.HeatData.S_psd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:28:09.537473+00:00
-- url     : https://prove2.me/theorems/e5a2118c-6cbe-452b-be01-f78f6c1a0767
-- title:
--   Heat Data: S psd
-- statement:
--   The Heat Data construction uses the S psd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3323-L3327
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3323-L3327

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

theorem Auto.HeatData.S_psd (hh : 0 ≤ Hd.h) (hσ : ∀ k, 0 < σ k) (v : Fin 3) (k : Fin 3) :
    (wGram (Hd.Bprev p σ v) (Hd.w p σ k)).PosSemidef ∧ (wGram (Hd.Bnext p σ v) (Hd.w p σ
      k)).PosSemidef := by sorry
