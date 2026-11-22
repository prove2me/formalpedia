-- Prove2me | Theorems.Thm_Auto_HeatData_Brow_update
-- name    : Auto.HeatData.Brow_update
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:27:58.173949+00:00
-- url     : https://prove2.me/theorems/95e88c57-1cd9-45c8-845c-be79da13db6a
-- title:
--   Heat Data: Brow update
-- statement:
--   The Heat Data construction uses the Brow update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3222-L3224
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3222-L3224

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

theorem Auto.HeatData.Brow_update (v : Fin 3) (q : ℝ) : Hd.Brow (Function.update p v q) σ v = Hd.Brow p σ v := by sorry
