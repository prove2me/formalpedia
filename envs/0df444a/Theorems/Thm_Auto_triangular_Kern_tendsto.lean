-- Prove2me | Theorems.Thm_Auto_triangular_Kern_tendsto
-- name    : Auto.triangular_Kern_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:56:37.1414+00:00
-- url     : https://prove2.me/theorems/5adfa768-cb55-45c1-8ea6-78d4882c7684
-- title:
--   Auto: triangular Kern tendsto
-- statement:
--   Source `dist`: Gaussian scales recover a fixed positive multiple of 1/t.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7861-L7876
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7861-L7876

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

theorem Auto.triangular_Kern_tendsto {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun n : ℕ => Kern 3 ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1) t) atTop (𝓝 (2 / ((63 / 20 : ℝ) *
      Real.sqrt (2 * Real.pi * (63 / 20)) * t))) := by sorry
