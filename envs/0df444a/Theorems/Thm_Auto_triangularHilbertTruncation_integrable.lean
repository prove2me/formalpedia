-- Prove2me | Theorems.Thm_Auto_triangularHilbertTruncation_integrable
-- name    : Auto.triangularHilbertTruncation_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:58:15.907913+00:00
-- url     : https://prove2.me/theorems/4861a4e1-8788-46f5-9e5f-f952cd7ad6e1
-- title:
--   Auto: triangular Hilbert Truncation integrable
-- statement:
--   The source's positive hard truncations are absolutely convergent.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8363-L8371
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8363-L8371

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

theorem Auto.triangularHilbertTruncation_integrable (F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ) {ε : ℝ}
    (hε : 0 < ε) :
    Integrable (fun q : (ℝ × ℝ) × ℝ => if ε < |q.1.1 + q.1.2 + q.2| then F₀ q.1 * F₁ (q.1.2,
      q.2) * F₂ (q.2, q.1.1) / ((q.1.1 + q.1.2 + q.2 : ℝ) : ℂ) else 0) := by sorry
