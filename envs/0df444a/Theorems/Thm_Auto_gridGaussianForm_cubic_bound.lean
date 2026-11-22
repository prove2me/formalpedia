-- Prove2me | Theorems.Thm_Auto_gridGaussianForm_cubic_bound
-- name    : Auto.gridGaussianForm_cubic_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T18:54:41.643137+00:00
-- url     : https://prove2.me/theorems/f2909973-baf7-4ef9-b662-fa46c8ca3b7c
-- title:
--   Auto: grid Gaussian Form cubic bound
-- statement:
--   Source Sections 2-3: the fixed Gaussian interval is bounded by the initial cubic energy.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7277-L7329
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7277-L7329

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

theorem Auto.gridGaussianForm_cubic_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Hd : HeatData ι) {kk : ι → ℤ} (hk : Function.Injective kk)
    (hu : ∀ i, Hd.u i = Hd.h * kk i) (hh : 0 < Hd.h)
    {a b : ℝ} (ha : Hd.h ^ 2 ≤ a) (hab : a ≤ b) :
    ‖gridGaussianForm Hd a b‖ ≤ heatBoundConstant * ∑ v, Hd.nCube v := by sorry
