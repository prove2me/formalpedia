-- Prove2me | Theorems.Thm_Auto_matCost_tendsto_regularization
-- name    : Auto.matCost_tendsto_regularization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:37:09.887976+00:00
-- url     : https://prove2.me/theorems/0affe36b-f93d-4a43-b401-5bc28aa96a48
-- title:
--   Auto: mat Cost tendsto regularization
-- statement:
--   The regularized spectral cost converges to the supported cost in source Section 1.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6979-L6988
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L6979-L6988

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
open MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section

theorem Auto.matCost_tendsto_regularization {n : Type*} [Fintype n] [DecidableEq n]
    {P : Matrix n n ℂ} (hP : P.PosSemidef) (K : Matrix n n ℂ)
    {η : ℕ → ℝ} (hη0 : ∀ m, 0 ≤ η m) (hη : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun m => matCost (P + (η m : ℂ) • 1) K) atTop (𝓝 (matCost P K)) := by sorry
