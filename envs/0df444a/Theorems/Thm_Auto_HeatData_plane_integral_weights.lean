-- Prove2me | Theorems.Thm_Auto_HeatData_plane_integral_weights
-- name    : Auto.HeatData.plane_integral_weights
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:52:24.167287+00:00
-- url     : https://prove2.me/theorems/5395dc51-71ab-46e9-aa31-22e71076bb06
-- title:
--   Heat Data: plane integral weights
-- statement:
--   The Heat Data construction uses the plane integral weights property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5743-L5767
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5743-L5767

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
omit [Fintype ι] [DecidableEq ι]

theorem Auto.HeatData.plane_integral_weights (α : Fin 3 → ℝ) (hα : ∀ k, 0 < α k) {β s : ℝ} (hβ : 0 < β)
    (hs : 0 < s) (v : Fin 3) (i j : ι) :
    Integrable (fun p : Fin 3 → ℝ => Gm β 0 s p * (Hd.w p (HeatData.sig α s) v i * Hd.w p
      (HeatData.sig α s) (v + 1) j)) ∧ ∫ p : Fin 3 → ℝ, Gm β 0 s p * (Hd.w p (HeatData.sig α s) v
      i * Hd.w p (HeatData.sig α s) (v + 1) j) = Hd.h ^ 2 := by sorry
