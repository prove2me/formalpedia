-- Prove2me | Theorems.Thm_Auto_triangularGaussianPrimitive_tendsto_top
-- name    : Auto.triangularGaussianPrimitive_tendsto_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:56:25.777103+00:00
-- url     : https://prove2.me/theorems/54262959-82f0-4d3b-a888-66c48bc4c18e
-- title:
--   Auto: triangular Gaussian Primitive tendsto top
-- statement:
--   The upper scale endpoint in the Hilbert-kernel recovery.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7838-L7846
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7838-L7846

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

theorem Auto.triangularGaussianPrimitive_tendsto_top {c : ℝ} (hc : 0 < c) (t : ℝ) :
    Tendsto (fun s => triangularGaussianPrimitive c s t) atTop (𝓝 (2 / (c * Real.sqrt (2 *
      Real.pi * c) * t))) := by sorry
