-- Prove2me | Theorems.Thm_Auto_HeatData_integral_Vbar_eq
-- name    : Auto.HeatData.integral_Vbar_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:52:49.236207+00:00
-- url     : https://prove2.me/theorems/7611feec-b829-491f-b9d5-1b61e807937c
-- title:
--   Heat Data: integral Vbar eq
-- statement:
--   The Heat Data construction uses the integral Vbar eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6148-L6163
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6148-L6163

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

theorem Auto.HeatData.integral_Vbar_eq (hh : 0 < Hd.h) {η : ℝ} (hη : 0 < η) {α : Fin 3 → ℝ} (hα1 : ∀ k, 1 ≤ α k)
    (hα2 : ∀ k, α k ≤ 2) {ta tb : ℝ} (hta : 0 < ta) (hab : ta ≤ tb) :
    ∫ s in ta..tb, ∑ v, Hd.Vbar α η v s = ∫ z, Hd.costDensity α η z ∂((volume.restrict (Set.Ioc
      ta tb)).prod volume) := by sorry
