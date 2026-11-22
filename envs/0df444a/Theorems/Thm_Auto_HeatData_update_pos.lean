-- Prove2me | Theorems.Thm_Auto_HeatData_update_pos
-- name    : Auto.HeatData.update_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:34:27.367773+00:00
-- url     : https://prove2.me/theorems/f6529308-4541-46db-847f-2c02515f4ed1
-- title:
--   Heat Data: update pos
-- statement:
--   The Heat Data construction uses the update pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3790-L3792
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3790-L3792

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

theorem Auto.HeatData.update_pos {σ : Fin 3 → ℝ} (hσ : ∀ k, 0 < σ k) (k : Fin 3) :
    ∀ j, 0 < (fun τ => Function.update σ k τ) (σ k) j := by sorry
