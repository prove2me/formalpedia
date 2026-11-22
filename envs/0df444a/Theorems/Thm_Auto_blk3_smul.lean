-- Prove2me | Theorems.Thm_Auto_blk3_smul
-- name    : Auto.blk3_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:43:56.506731+00:00
-- url     : https://prove2.me/theorems/306099ce-2f42-4272-af37-e82393b7ff3c
-- title:
--   Auto: blk3 smul
-- statement:
--   The Auto construction uses the blk3 smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2564-L2566
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2564-L2566

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
omit [DecidableEq ι] [Fintype ι]

theorem Auto.blk3_smul (c : ℂ) (X : Matrix (Fin 3) (Fin 3) (Matrix ι ι ℂ)) :
    blk3 (c • X) = c • blk3 X := by sorry
