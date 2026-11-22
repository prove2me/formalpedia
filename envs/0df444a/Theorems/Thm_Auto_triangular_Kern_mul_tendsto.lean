-- Prove2me | Theorems.Thm_Auto_triangular_Kern_mul_tendsto
-- name    : Auto.triangular_Kern_mul_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:56:34.663242+00:00
-- url     : https://prove2.me/theorems/52533927-c734-4ec1-833a-1fb54ffd165e
-- title:
--   Auto: triangular Kern mul tendsto
-- statement:
--   The normalized cancellation multipliers converge away from the singular plane.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7911-L7916
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7911-L7916

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

theorem Auto.triangular_Kern_mul_tendsto {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun n : ℕ => t * Kern 3 ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1) t) atTop (𝓝
      triangularKernelCoefficient) := by sorry
