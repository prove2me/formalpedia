-- Prove2me | Theorems.Thm_Auto_blk3_mul
-- name    : Auto.blk3_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:27:00.732562+00:00
-- url     : https://prove2.me/theorems/2685fac5-dd8a-4aef-b290-18a2094ecdd0
-- title:
--   Auto: blk3 mul
-- statement:
--   The Auto construction uses the blk3 mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2407-L2408
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2407-L2408

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
omit [DecidableEq ι]

theorem Auto.blk3_mul (X Y : Matrix (Fin 3) (Fin 3) (Matrix ι ι ℂ)) :
    blk3 (X * Y) = blk3 X * blk3 Y := by sorry
