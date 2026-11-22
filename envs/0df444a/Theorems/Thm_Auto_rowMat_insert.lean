-- Prove2me | Theorems.Thm_Auto_rowMat_insert
-- name    : Auto.rowMat_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:31:25.657885+00:00
-- url     : https://prove2.me/theorems/18abb154-9faf-42cd-836d-718f33bc9b87
-- title:
--   Auto: row Mat insert
-- statement:
--   The Auto construction uses the row Mat insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2492-L2496
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2492-L2496

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

theorem Auto.rowMat_insert (W V D : Matrix ι ι ℂ) :
    (rowMat W V)ᴴ * D * rowMat W V = Matrix.fromBlocks (Wᴴ * D * W) (Wᴴ * D * Vᴴ) (V * D * W) (V
      * D * Vᴴ) := by sorry
