-- Prove2me | Theorems.Thm_Auto_energy_conjTranspose_mul_self_le
-- name    : Auto.energy_conjTranspose_mul_self_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:40:36.85708+00:00
-- url     : https://prove2.me/theorems/e1a70d7e-603d-408f-bbed-f08d9da66c7b
-- title:
--   Auto: energy conj Transpose mul self le
-- statement:
--   The Auto construction uses the energy conj Transpose mul self le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L763-L783
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L763-L783

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
open Auto
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
omit [DecidableEq m]

theorem Auto.energy_conjTranspose_mul_self_le (R : Matrix m n ℂ) :
    energy (Rᴴ * R) ≤ hsSq R ^ (3 / 2 : ℝ) := by sorry
