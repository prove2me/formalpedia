-- Prove2me | Theorems.Thm_Auto_HeatData_Jbar_integrable
-- name    : Auto.HeatData.Jbar_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:52:32.919158+00:00
-- url     : https://prove2.me/theorems/b71c5dfe-4ef3-450b-bd38-1f6b30ef1d7f
-- title:
--   Heat Data: Jbar integrable
-- statement:
--   The Heat Data construction uses the Jbar integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5886-L5897
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5886-L5897

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
variable (Hd : HeatData ι) {kk : ι → ℤ}

theorem Auto.HeatData.Jbar_integrable (hh : 0 < Hd.h) {η : ℝ} (hη : 0 < η) {α : Fin 3 → ℝ} (hα1 : ∀ k, 1 ≤ α k)
    (hα2 : ∀ k, α k ≤ 2) {s : ℝ} (hs : 0 < s) :
    Integrable (fun p => Gm (1 / 10) 0 s p * ∑ v, Hd.qE α η v s p) := by sorry
