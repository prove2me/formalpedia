-- Prove2me | Theorems.Thm_Auto_matCost_le_liminf
-- name    : Auto.matCost_le_liminf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:36:55.912418+00:00
-- url     : https://prove2.me/theorems/55634f5e-688d-473b-81bd-e5ffcbaf0838
-- title:
--   Auto: mat Cost le liminf
-- statement:
--   The Auto construction uses the mat Cost le liminf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5964-L5977
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5964-L5977

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
open Auto
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem Auto.matCost_le_liminf {P : Matrix n n ℂ} (hP : P.PosSemidef) (K : Matrix n n ℂ) {η : ℕ → ℝ}
    (hη0 : ∀ m, 0 ≤ η m) (hη : Tendsto η atTop (𝓝 0)) :
    matCost P K ≤ liminf (fun m => matCost (P + (η m : ℂ) • 1) K) atTop := by sorry
