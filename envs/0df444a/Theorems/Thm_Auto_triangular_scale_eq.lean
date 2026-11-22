-- Prove2me | Theorems.Thm_Auto_triangular_scale_eq
-- name    : Auto.triangular_scale_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:57:49.166359+00:00
-- url     : https://prove2.me/theorems/4224a875-cba0-4a22-9e8d-6df330dae5e7
-- title:
--   Auto: triangular scale eq
-- statement:
--   The Gaussian pairing agrees with the cancelled expression.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8257-L8268
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8257-L8268

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

theorem Auto.triangular_scale_eq (H F G : SchwartzMap (ℝ × ℝ) ℂ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ q : (ℝ × ℝ) × ℝ, H q.1 * triangularShiftProduct F G q.1 q.2 * (Kern 3 a b q.2 : ℂ)) = (2
      : ℂ)⁻¹ * ∫ q : (ℝ × ℝ) × ℝ, triangularOddQuotient H F G q * ((q.2 * Kern 3 a b q.2 : ℝ) : ℂ)
          := by sorry
