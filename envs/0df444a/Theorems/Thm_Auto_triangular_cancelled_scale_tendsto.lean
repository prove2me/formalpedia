-- Prove2me | Theorems.Thm_Auto_triangular_cancelled_scale_tendsto
-- name    : Auto.triangular_cancelled_scale_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:57:46.813779+00:00
-- url     : https://prove2.me/theorems/e7e6087c-563e-4506-9439-d7877c329aaf
-- title:
--   Auto: triangular cancelled scale tendsto
-- statement:
--   The cancelled scale kernels converge to the principal-value candidate.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8140-L8147
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8140-L8147

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

theorem Auto.triangular_cancelled_scale_tendsto (H F G : SchwartzMap (ℝ × ℝ) ℂ) :
    Tendsto (fun n : ℕ => (2 : ℂ)⁻¹ * ∫ q : (ℝ × ℝ) × ℝ, triangularOddQuotient H F G q * ((q.2 *
      Kern 3 ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1) q.2 : ℝ) : ℂ)) atTop (𝓝 ((triangularKernelCoefficient :
      ℂ) * triangularPV H F G)) := by sorry
