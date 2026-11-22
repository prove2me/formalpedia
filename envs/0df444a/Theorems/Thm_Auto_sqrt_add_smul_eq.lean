-- Prove2me | Theorems.Thm_Auto_sqrt_add_smul_eq
-- name    : Auto.sqrt_add_smul_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:52:32.500864+00:00
-- url     : https://prove2.me/theorems/191f86e1-1167-4b78-a620-8170fb154c4d
-- title:
--   Auto: sqrt add smul eq
-- statement:
--   The Auto construction uses the sqrt add smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5915-L5947
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L5915-L5947

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

theorem Auto.sqrt_add_smul_eq {P : Matrix n n ℂ} (hP : P.PosSemidef) {η : ℝ} (hη : 0 ≤ η) :
    CFC.sqrt (P + (η : ℂ) • 1) = (hP.1.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i =>
      ((√(hP.1.eigenvalues i + η) : ℝ) : ℂ)) * star (hP.1.eigenvectorUnitary : Matrix n n ℂ) := by sorry
