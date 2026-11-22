-- Prove2me | Theorems.Thm_Auto_triangular_product_integrable
-- name    : Auto.triangular_product_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:37:37.718346+00:00
-- url     : https://prove2.me/theorems/97f4d0fe-8ccd-443f-8471-f958713d4c21
-- title:
--   Auto: triangular product integrable
-- statement:
--   Absolute integrability of the unweighted Schwartz product in sheared coordinates.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8150-L8165
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8150-L8165

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

theorem Auto.triangular_product_integrable (H F G : SchwartzMap (ℝ × ℝ) ℂ) :
    Integrable (fun q : (ℝ × ℝ) × ℝ => H q.1 * triangularShiftProduct F G q.1 q.2) := by sorry
