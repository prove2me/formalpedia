-- Prove2me | Theorems.Thm_Auto_triangularGaussianPrimitive_tendsto_zero
-- name    : Auto.triangularGaussianPrimitive_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:56:31.433712+00:00
-- url     : https://prove2.me/theorems/7710f76b-d082-4d68-b529-e87cf1809801
-- title:
--   Auto: triangular Gaussian Primitive tendsto zero
-- statement:
--   The lower scale endpoint in the Hilbert-kernel recovery.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7849-L7858
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7849-L7858

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

theorem Auto.triangularGaussianPrimitive_tendsto_zero {c t : ℝ} (hc : 0 < c) (ht : t ≠ 0) :
    Tendsto (fun s => triangularGaussianPrimitive c s t) (𝓝[>] 0) (𝓝 0) := by sorry
