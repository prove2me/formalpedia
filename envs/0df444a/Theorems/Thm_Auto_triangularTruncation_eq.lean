-- Prove2me | Theorems.Thm_Auto_triangularTruncation_eq
-- name    : Auto.triangularTruncation_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:57:48.709927+00:00
-- url     : https://prove2.me/theorems/e65631e2-a1a5-4a92-a804-98aaf8f689ea
-- title:
--   Auto: triangular Truncation eq
-- statement:
--   Reflection turns a hard truncation into an integrable odd difference quotient.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8200-L8209
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8200-L8209

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

theorem Auto.triangularTruncation_eq (H F G : SchwartzMap (ℝ × ℝ) ℂ) {ε : ℝ} (hε : 0 < ε) :
    triangularTruncation H F G ε = (2 : ℂ)⁻¹ * ∫ q : (ℝ × ℝ) × ℝ, if ε < |q.2| then
      triangularOddQuotient H F G q else 0 := by sorry
