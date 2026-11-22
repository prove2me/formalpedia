-- Prove2me | Theorems.Thm_Auto_triangularTruncation_tendsto
-- name    : Auto.triangularTruncation_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:57:56.194571+00:00
-- url     : https://prove2.me/theorems/87a82f44-0bf7-485c-8f2f-f4ce92b5a9ec
-- title:
--   Auto: triangular Truncation tendsto
-- statement:
--   Source equation `dist`: symmetric hard truncations converge for Schwartz inputs.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8212-L8233
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8212-L8233

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

theorem Auto.triangularTruncation_tendsto (H F G : SchwartzMap (ℝ × ℝ) ℂ) :
    Tendsto (triangularTruncation H F G) (𝓝[>] (0 : ℝ)) (𝓝 (triangularPV H F G)) := by sorry
