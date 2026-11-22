-- Prove2me | Theorems.Thm_Auto_HeatData_T_update
-- name    : Auto.HeatData.T_update
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:45:01.831748+00:00
-- url     : https://prove2.me/theorems/41a6de69-fe0f-4a7d-83d9-f02d4d4a042f
-- title:
--   Heat Data: T update
-- statement:
--   The Heat Data construction uses the T update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3246-L3248
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3246-L3248

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

theorem Auto.HeatData.T_update (hh : 0 ≤ Hd.h) (hσ : ∀ k, 0 < σ k) (v : Fin 3) (q : ℝ) :
    Hd.T (Function.update p v q) σ v = 0 + wGram (Hd.Brow p σ v) (gweight Hd.u Hd.h (σ v) q) := by sorry
