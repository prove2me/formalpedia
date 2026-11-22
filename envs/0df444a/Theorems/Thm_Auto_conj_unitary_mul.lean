-- Prove2me | Theorems.Thm_Auto_conj_unitary_mul
-- name    : Auto.conj_unitary_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:44:08.153723+00:00
-- url     : https://prove2.me/theorems/4ecee2a8-9b50-4e91-9912-b2f6e5b8133d
-- title:
--   Auto: conj unitary mul
-- statement:
--   The Auto construction uses the conj unitary mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2613-L2621
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2613-L2621

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
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1611
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1612
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (W0 W1 W2 D0 D1 D2 : Matrix ι ι ℂ)

theorem Auto.conj_unitary_mul {κ : Type*} [Fintype κ] [DecidableEq κ] (U : Matrix.unitaryGroup κ ℂ)
    (X Y : Matrix κ κ ℂ) :
    star (U : Matrix κ κ ℂ) * (X * Y) * (U : Matrix κ κ ℂ) = (star (U : Matrix κ κ ℂ) * X * U) *
      (star (U : Matrix κ κ ℂ) * Y * U) := by sorry
