-- Prove2me | Theorems.Thm_Auto_gridGaussianForm_eq
-- name    : Auto.gridGaussianForm_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:54:38.39914+00:00
-- url     : https://prove2.me/theorems/8ec2cee0-5022-46f9-9b82-f827459bca00
-- title:
--   Auto: grid Gaussian Form eq
-- statement:
--   The Auto construction uses the grid Gaussian Form eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7231-L7265
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7231-L7265

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
public section
open scoped ENNReal NNReal
open MeasureTheory Filter Topology Real
public section
open Auto
open MeasureTheory Filter Topology Matrix Real
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section

theorem Auto.gridGaussianForm_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Hd : HeatData ι) (hh : 0 < Hd.h) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    gridGaussianForm Hd a b =
      ∫ s in Set.Ioc a b, ((1 / s : ℝ) : ℂ) *
        ∫ q : Fin 2 → ℝ, Hd.baseTrace 3 (planePt q) s := by sorry
