-- Prove2me | Theorems.Thm_Auto_triangular_trilinear_dense_extension
-- name    : Auto.triangular_trilinear_dense_extension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:58:30.585799+00:00
-- url     : https://prove2.me/theorems/950d9fa9-0c49-4e9e-8b3d-b733592e15ff
-- title:
--   Auto: triangular trilinear dense extension
-- statement:
--   Source Theorem 1: a norm-controlled trilinear map extends uniquely along a dense linear map.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8586-L8624
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8586-L8624

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
variable {𝕜 E V W : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W] [CompleteSpace
    W]

theorem Auto.triangular_trilinear_dense_extension (e : E →ₗ[𝕜] V) (hd : DenseRange e)
    (T : E →ₗ[𝕜] E →ₗ[𝕜] E →ₗ[𝕜] W) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ a b c, ‖T a b c‖ ≤ C * ‖e a‖ * ‖e b‖ * ‖e c‖) :
    ∃ T' : V →L[𝕜] V →L[𝕜] V →L[𝕜] W, (∀ a b c, T' (e a) (e b) (e c) = T a b c) ∧ (∀ x y z, ‖T'
      x y z‖ ≤ C * ‖x‖ * ‖y‖ * ‖z‖) ∧ ∀ S : V →L[𝕜] V →L[𝕜] V →L[𝕜] W, (∀ a b c, S (e a) (e b) (e
      c) = T a b c) → S = T' := by sorry
