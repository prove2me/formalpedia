-- Prove2me | Theorems.Thm_Auto_blk3_diag_eq
-- name    : Auto.blk3_diag_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:43:24.880865+00:00
-- url     : https://prove2.me/theorems/875b687d-ed19-4a36-b57b-e05231c304cb
-- title:
--   Auto: blk3 diag eq
-- statement:
--   The Auto construction uses the blk3 diag eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2474-L2481
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2474-L2481

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

theorem Auto.blk3_diag_eq (X0 X1 X2 : Matrix ι ι ℂ) :
    blk3 !![X0, 0, 0; 0, X1, 0; 0, 0, X2] = emb1 (ι := ι) 0 * X0 * (emb1 (ι := ι) 0)ᴴ + emb1 (ι :=
        ι) 1 * X1 * (emb1 (ι := ι) 1)ᴴ +
        emb1 (ι := ι) 2 * X2 * (emb1 (ι := ι) 2)ᴴ := by sorry
