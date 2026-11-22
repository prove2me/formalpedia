-- Prove2me | Theorems.Thm_Auto_triangularGaussianPrimitive_eq_profile
-- name    : Auto.triangularGaussianPrimitive_eq_profile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:29:08.709496+00:00
-- url     : https://prove2.me/theorems/394a6492-0311-44ca-96dc-3194d8818376
-- title:
--   Auto: triangular Gaussian Primitive eq profile
-- statement:
--   The Auto construction uses the triangular Gaussian Primitive eq profile property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7832-L7835
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7832-L7835

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

theorem Auto.triangularGaussianPrimitive_eq_profile (c s t : ℝ) :
    triangularGaussianPrimitive c s t = (2 / (c * Real.sqrt (2 * Real.pi * c) * t)) *
      triangularCutoffProfile (t ^ 2 / (2 * c * s)) := by sorry
