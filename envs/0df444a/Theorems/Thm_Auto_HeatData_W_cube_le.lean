-- Prove2me | Theorems.Thm_Auto_HeatData_W_cube_le
-- name    : Auto.HeatData.W_cube_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:52:07.706301+00:00
-- url     : https://prove2.me/theorems/8670aef4-62eb-4797-a771-985d7089fe57
-- title:
--   Heat Data: W cube le
-- statement:
--   The Heat Data construction uses the W cube le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5659-L5700
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5659-L5700

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
variable (Hd : HeatData ι)

theorem Auto.HeatData.W_cube_le (hh : 0 ≤ Hd.h) (p σ : Fin 3 → ℝ) (v : Fin 3) {M : ℝ} (hM : 0 ≤ M)
    (h1 : ∑ i, Hd.w p σ v i ≤ M) (h2 : ∑ j, Hd.w p σ (v + 1) j ≤ M) :
    hsSq (Hd.W p σ v) ^ (3 / 2 : ℝ) ≤ M * ∑ i, ∑ j, ‖Hd.A v i j‖ ^ 3 * Hd.w p σ v i * Hd.w p σ
      (v + 1) j := by sorry
