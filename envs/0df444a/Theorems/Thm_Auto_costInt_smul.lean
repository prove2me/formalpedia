-- Prove2me | Theorems.Thm_Auto_costInt_smul
-- name    : Auto.costInt_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:42:28.342943+00:00
-- url     : https://prove2.me/theorems/f301b5e3-3648-4e3c-bb9a-06cc76f88dd1
-- title:
--   Auto: cost Int smul
-- statement:
--   The Auto construction uses the cost Int smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1889-L1895
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1889-L1895

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
variable {n : Type*} [Fintype n] [DecidableEq n]
omit [DecidableEq n]

theorem Auto.costInt_smul (A K X : Matrix n n ℂ) (c : ℝ) :
    costInt A (c • K) (c • X) = c ^ 2 * costInt A K X := by sorry
