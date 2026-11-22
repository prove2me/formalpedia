-- Prove2me | Theorems.Thm_Auto_triangular_snd_ne_zero
-- name    : Auto.triangular_snd_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:29:17.449211+00:00
-- url     : https://prove2.me/theorems/bc7af08c-8a47-4125-a85d-75c2d1105d45
-- title:
--   Auto: triangular snd ne zero
-- statement:
--   The singular coordinate is nonzero almost everywhere.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8131-L8133
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8131-L8133

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

theorem Auto.triangular_snd_ne_zero : ∀ᵐ q : (ℝ × ℝ) × ℝ, q.2 ≠ 0 := by sorry
