-- Prove2me | Theorems.Thm_Auto_triangular_integral_symmetrize
-- name    : Auto.triangular_integral_symmetrize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:37:45.635097+00:00
-- url     : https://prove2.me/theorems/7ae92582-dabd-4511-8816-c736141b8499
-- title:
--   Auto: triangular integral symmetrize
-- statement:
--   Symmetrization of any integrable function in the singular coordinate.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8168-L8175
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8168-L8175

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

theorem Auto.triangular_integral_symmetrize {f : (ℝ × ℝ) × ℝ → ℂ} (hf : Integrable f) :
    ∫ q, f q = (2 : ℂ)⁻¹ * ∫ q, (f q + f (q.1, -q.2)) := by sorry
