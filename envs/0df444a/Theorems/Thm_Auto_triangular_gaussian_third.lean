-- Prove2me | Theorems.Thm_Auto_triangular_gaussian_third
-- name    : Auto.triangular_gaussian_third
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:37:22.744987+00:00
-- url     : https://prove2.me/theorems/213439bb-4e0c-41c0-805d-fbad8f3a3979
-- title:
--   Auto: triangular gaussian third
-- statement:
--   The explicit third derivative used in source Section 3, equation `dist`.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7760-L7770
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7760-L7770

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

theorem Auto.triangular_gaussian_third {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    gaussianD 3 σ t = (3 * t / σ ^ 2 - t ^ 3 / σ ^ 3) * gaussian σ t := by sorry
