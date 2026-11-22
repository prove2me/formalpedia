-- Prove2me | Theorems.Thm_Auto_rowMat_gram
-- name    : Auto.rowMat_gram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:31:30.637267+00:00
-- url     : https://prove2.me/theorems/6c1742c2-eb9c-4e92-87b2-7ea87c259814
-- title:
--   Auto: row Mat gram
-- statement:
--   The Auto construction uses the row Mat gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2499-L2501
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2499-L2501

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

theorem Auto.rowMat_gram (W V : Matrix ι ι ℂ) :
    (rowMat W V)ᴴ * rowMat W V = Matrix.fromBlocks (Wᴴ * W) (Wᴴ * Vᴴ) (V * W) (V * Vᴴ) := by sorry
