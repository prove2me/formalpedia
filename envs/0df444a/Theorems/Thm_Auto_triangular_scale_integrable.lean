-- Prove2me | Theorems.Thm_Auto_triangular_scale_integrable
-- name    : Auto.triangular_scale_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:38:06.253357+00:00
-- url     : https://prove2.me/theorems/0d75f7e6-fe86-4f21-8e18-8ffcc89ce455
-- title:
--   Auto: triangular scale integrable
-- statement:
--   Absolute convergence of a Gaussian scale pairing for Schwartz inputs.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8245-L8254
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8245-L8254

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

theorem Auto.triangular_scale_integrable (H F G : SchwartzMap (ℝ × ℝ) ℂ) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    Integrable (fun q : (ℝ × ℝ) × ℝ => H q.1 * triangularShiftProduct F G q.1 q.2 * (Kern 3 a b
      q.2 : ℂ)) := by sorry
