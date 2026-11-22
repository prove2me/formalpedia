-- Prove2me | Theorems.Thm_Auto_matCost_eq_sylv
-- name    : Auto.matCost_eq_sylv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:34:48.151723+00:00
-- url     : https://prove2.me/theorems/c8aa8516-90e6-42c1-bae6-12fd2b1e246b
-- title:
--   Auto: mat Cost eq sylv
-- statement:
--   The Auto construction uses the mat Cost eq sylv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3989-L4010
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L3989-L4010

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
open Auto
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem Auto.matCost_eq_sylv {P : Matrix n n ℂ} {η : ℝ} (hη : 0 < η)
    (hP : (P - (η : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) (K : Matrix n n ℂ) :
    matCost P K = ENNReal.ofReal ((3 / 2) * hsRe K (sylvSol (CFC.sqrt P) K)) := by sorry
