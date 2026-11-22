-- Prove2me | Theorems.Thm_Auto_triangularGaussianPrimitive_hasDerivAt
-- name    : Auto.triangularGaussianPrimitive_hasDerivAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:56:11.761013+00:00
-- url     : https://prove2.me/theorems/f4ab73d9-9906-46f2-96fa-c065f3dd4bd1
-- title:
--   Auto: triangular Gaussian Primitive has Deriv At
-- statement:
--   Source `dist`: the scale primitive differentiates to the third Gaussian kernel.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7778-L7795
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7778-L7795

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

theorem Auto.triangularGaussianPrimitive_hasDerivAt {c s t : ℝ} (hc : 0 < c) (hs : 0 < s)
    (ht : t ≠ 0) :
    HasDerivAt (fun u => triangularGaussianPrimitive c u t) (Real.sqrt s ^ 3 * gaussianD 3 (c *
      s) t / s) s := by sorry
