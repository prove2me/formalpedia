-- Prove2me | Theorems.Thm_Auto_triangular_Kern_mul_bound
-- name    : Auto.triangular_Kern_mul_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:56:39.536984+00:00
-- url     : https://prove2.me/theorems/50f067ce-f5d7-4db5-8397-084673938193
-- title:
--   Auto: triangular Kern mul bound
-- statement:
--   Cancellation leaves a uniformly bounded multiplier, independent of scale.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7887-L7908
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7887-L7908

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

theorem Auto.triangular_Kern_mul_bound {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (t : ℝ) :
    |t * Kern 3 a b t| ≤ 6 * triangularKernelCoefficient := by sorry
