-- Prove2me | Theorems.Thm_Auto_triangular_scale_tendsto
-- name    : Auto.triangular_scale_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:57:51.999843+00:00
-- url     : https://prove2.me/theorems/e8e81427-4b1e-4cc4-b6dd-bad720222227
-- title:
--   Auto: triangular scale tendsto
-- statement:
--   Source equation `dist`: the Gaussian scale limit is the symmetric principal value.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8271-L8279
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8271-L8279

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

theorem Auto.triangular_scale_tendsto (H F G : SchwartzMap (ℝ × ℝ) ℂ) :
    Tendsto (fun n : ℕ => ∫ q : (ℝ × ℝ) × ℝ, H q.1 * triangularShiftProduct F G q.1 q.2 * (Kern
      3 ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1) q.2 : ℂ)) atTop (𝓝 ((triangularKernelCoefficient : ℂ) *
      triangularPV H F G)) := by sorry
