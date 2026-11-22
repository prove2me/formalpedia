-- Prove2me | Theorems.Thm_Auto_triangular_truncation_integrable
-- name    : Auto.triangular_truncation_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:37:47.539093+00:00
-- url     : https://prove2.me/theorems/ccc2f7ef-926a-4cc9-8de4-c74ae3fa5610
-- title:
--   Auto: triangular truncation integrable
-- statement:
--   Every positive hard truncation is an absolutely convergent integral.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8183-L8197
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8183-L8197

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

theorem Auto.triangular_truncation_integrable (H F G : SchwartzMap (ℝ × ℝ) ℂ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun q : (ℝ × ℝ) × ℝ => if ε < |q.2| then H q.1 * triangularShiftProduct F G q.1
      q.2 / (q.2 : ℂ) else 0) := by sorry
