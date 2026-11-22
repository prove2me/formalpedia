-- Prove2me | Theorems.Thm_Auto_triangular_Kern_odd
-- name    : Auto.triangular_Kern_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:37:48.902744+00:00
-- url     : https://prove2.me/theorems/4a280944-0443-4dba-91e0-7ded6e023aaf
-- title:
--   Auto: triangular Kern odd
-- statement:
--   The third-derivative Gaussian interval kernels are odd.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8236-L8242
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L8236-L8242

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

theorem Auto.triangular_Kern_odd {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (t : ℝ) :
    Kern 3 a b (-t) = -Kern 3 a b t := by sorry
