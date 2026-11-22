-- Prove2me | Theorems.Thm_Auto_HeatData_ofReal_integral_Vbar
-- name    : Auto.HeatData.ofReal_integral_Vbar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:52:51.544471+00:00
-- url     : https://prove2.me/theorems/41ffb52f-5a2b-408c-bb77-49f7686bbbac
-- title:
--   Heat Data: of Real integral Vbar
-- statement:
--   The Heat Data construction uses the of Real integral Vbar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6165-L6173
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6165-L6173

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
variable (Hd : HeatData ι)

theorem Auto.HeatData.ofReal_integral_Vbar (hh : 0 < Hd.h) {η : ℝ} (hη : 0 < η) {α : Fin 3 → ℝ}
    (hα1 : ∀ k, 1 ≤ α k) (hα2 : ∀ k, α k ≤ 2) {ta tb : ℝ} (hta : 0 < ta) (hab : ta ≤ tb) :
    ENNReal.ofReal (∫ s in ta..tb, ∑ v, Hd.Vbar α η v s) = ∫⁻ z, ENNReal.ofReal (Gm (1 / 10) 0
      z.1 z.2) * ∑ v, matCost (Hd.T z.2 (sig α z.1) v + (η : ℂ) • 1) (Hd.Ui z.2 (sig α z.1) v)
      ∂((volume.restrict (Set.Ioc ta tb)).prod volume) := by sorry
