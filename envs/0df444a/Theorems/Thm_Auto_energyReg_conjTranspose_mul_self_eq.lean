-- Prove2me | Theorems.Thm_Auto_energyReg_conjTranspose_mul_self_eq
-- name    : Auto.energyReg_conjTranspose_mul_self_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:40:42.803811+00:00
-- url     : https://prove2.me/theorems/88ae1fb9-0718-45b8-8caf-f19d57598785
-- title:
--   Auto: energy Reg conj Transpose mul self eq
-- statement:
--   The Auto construction uses the energy Reg conj Transpose mul self eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L758-L760
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L758-L760

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

theorem Auto.energyReg_conjTranspose_mul_self_eq (η : ℝ) (R : Matrix m n ℂ) :
    energyReg η (Rᴴ * R) = energyReg η (R * Rᴴ) := by sorry
