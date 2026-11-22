-- Prove2me | Theorems.Thm_Auto_trF_conjTranspose_mul_self_eq
-- name    : Auto.trF_conjTranspose_mul_self_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:40:31.486407+00:00
-- url     : https://prove2.me/theorems/060e6e79-efdb-470b-8a7a-fcee19609d7e
-- title:
--   Auto: tr F conj Transpose mul self eq
-- statement:
--   The Auto construction uses the tr F conj Transpose mul self eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L727-L747
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L727-L747

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

theorem Auto.trF_conjTranspose_mul_self_eq (f : ℝ → ℝ) (hf : f 0 = 0) (R : Matrix m n ℂ) :
    trF f (Rᴴ * R) = trF f (R * Rᴴ) := by sorry
