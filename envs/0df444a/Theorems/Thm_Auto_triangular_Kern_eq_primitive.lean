-- Prove2me | Theorems.Thm_Auto_triangular_Kern_eq_primitive
-- name    : Auto.triangular_Kern_eq_primitive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:37:24.008125+00:00
-- url     : https://prove2.me/theorems/b63f4af5-3991-494e-a184-6a9dcab8993d
-- title:
--   Auto: triangular Kern eq primitive
-- statement:
--   Source `dist`: the Gaussian interval kernel is the difference of its scale primitives.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7799-L7812
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7799-L7812

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
set_option maxHeartbeats 2000000

theorem Auto.triangular_Kern_eq_primitive {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {t : ℝ} (ht : t ≠ 0) :
    Kern 3 a b t = triangularGaussianPrimitive (63 / 20) b t - triangularGaussianPrimitive (63 /
      20) a t := by sorry
