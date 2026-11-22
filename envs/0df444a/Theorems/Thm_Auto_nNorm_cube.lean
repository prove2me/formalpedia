-- Prove2me | Theorems.Thm_Auto_nNorm_cube
-- name    : Auto.nNorm_cube
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:54:44.817831+00:00
-- url     : https://prove2.me/theorems/479d8f5a-316c-4e80-b6ef-1dd5646fa878
-- title:
--   Auto: n Norm cube
-- statement:
--   The Auto construction uses the n Norm cube property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7331-L7335
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L7331-L7335

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

theorem Auto.nNorm_cube {ι : Type*} [Fintype ι] (h : ℝ) (A : Matrix ι ι ℂ) :
    nNorm h A ^ 3 = h ^ 2 * ∑ i, ∑ j, ‖A i j‖ ^ 3 := by sorry
