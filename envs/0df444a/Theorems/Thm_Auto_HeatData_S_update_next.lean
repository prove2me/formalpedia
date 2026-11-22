-- Prove2me | Theorems.Thm_Auto_HeatData_S_update_next
-- name    : Auto.HeatData.S_update_next
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:33:34.528465+00:00
-- url     : https://prove2.me/theorems/1c61481f-901e-455e-a2f4-8473067c1a4a
-- title:
--   Heat Data: S update next
-- statement:
--   The Heat Data construction uses the S update next property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3254-L3259
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3254-L3259

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

theorem Auto.HeatData.S_update_next (hh : 0 ≤ Hd.h) (hσ : ∀ k, 0 < σ k) (v : Fin 3) (q : ℝ) :
    Hd.S (Function.update p (v + 1) q) σ v = wGram (Hd.Bprev p σ v) (Hd.w p σ (v - 1)) + wGram
      (Hd.Bnext p σ v) (gweight Hd.u Hd.h (σ (v + 1)) q) := by sorry
