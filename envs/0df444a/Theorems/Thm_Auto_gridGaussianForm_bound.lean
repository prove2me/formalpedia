-- Prove2me | Theorems.Thm_Auto_gridGaussianForm_bound
-- name    : Auto.gridGaussianForm_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:54:57.325808+00:00
-- url     : https://prove2.me/theorems/8592fa41-797e-4ac7-a4f8-50be21da692e
-- title:
--   Auto: grid Gaussian Form bound
-- statement:
--   Trilinearity converts the cubic energy estimate to the source's product of three L3 norms.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7358-L7410
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7358-L7410

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

theorem Auto.gridGaussianForm_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Hd : HeatData ι) {kk : ι → ℤ} (hk : Function.Injective kk)
    (hu : ∀ i, Hd.u i = Hd.h * kk i) (hh : 0 < Hd.h)
    {a b : ℝ} (ha : Hd.h ^ 2 ≤ a) (hab : a ≤ b) :
    ‖gridGaussianForm Hd a b‖ ≤ 3 * heatBoundConstant *
      nNorm Hd.h (Hd.A 0) * nNorm Hd.h (Hd.A 1) * nNorm Hd.h (Hd.A 2) := by sorry
