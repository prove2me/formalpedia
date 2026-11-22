-- Prove2me | Theorems.Thm_Auto_blk3_add
-- name    : Auto.blk3_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:42:55.277812+00:00
-- url     : https://prove2.me/theorems/e843872e-f2d4-401c-b289-db8aa3b15a97
-- title:
--   Auto: blk3 add
-- statement:
--   The Auto construction uses the blk3 add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2411-L2413
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2411-L2413

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
omit [DecidableEq ι] [Fintype ι]

theorem Auto.blk3_add (X Y : Matrix (Fin 3) (Fin 3) (Matrix ι ι ℂ)) :
    blk3 (X + Y) = blk3 X + blk3 Y := by sorry
