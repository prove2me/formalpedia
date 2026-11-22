-- Prove2me | Theorems.Thm_Auto_triangular_bilinear_dense_extension
-- name    : Auto.triangular_bilinear_dense_extension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:58:26.414686+00:00
-- url     : https://prove2.me/theorems/8cc9fe54-039f-4cd1-aa9a-5b271cab6e8a
-- title:
--   Auto: triangular bilinear dense extension
-- statement:
--   Extend a bounded bilinear form along a dense linear map.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8565-L8583
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8565-L8583

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

theorem Auto.triangular_bilinear_dense_extension (e : E →ₗ[𝕜] V) (hd : DenseRange e)
    (B : E →ₗ[𝕜] E →ₗ[𝕜] W) {C : ℝ} (hC : 0 ≤ C) (hB : ∀ a b, ‖B a b‖ ≤ C * ‖e a‖ * ‖e b‖) :
    ∃ B' : V →L[𝕜] V →L[𝕜] W, (∀ a b, B' (e a) (e b) = B a b) ∧ ∀ x, ‖B' x‖ ≤ C * ‖x‖ := by sorry
