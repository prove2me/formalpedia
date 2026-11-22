-- Prove2me | Theorems.Thm_Auto_gridGaussianForm_scale
-- name    : Auto.gridGaussianForm_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:54:50.704439+00:00
-- url     : https://prove2.me/theorems/0c244a94-a7ab-47f6-ba24-efef3b91ee83
-- title:
--   Auto: grid Gaussian Form scale
-- statement:
--   The Auto construction uses the grid Gaussian Form scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7340-L7347
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7340-L7347

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

theorem Auto.gridGaussianForm_scale {ι : Type*} [Fintype ι]
    (Hd : HeatData ι) (c : Fin 3 → ℂ) (a b : ℝ) :
    gridGaussianForm (scaleHeatData Hd c) a b =
      c 0 * c 1 * c 2 * gridGaussianForm Hd a b := by sorry
