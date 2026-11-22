-- Prove2me | Theorems.Thm_Auto_matCost_anti
-- name    : Auto.matCost_anti
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:24:29.319705+00:00
-- url     : https://prove2.me/theorems/184ab17e-158f-449f-8e1b-3e2427ed2d78
-- title:
--   Auto: mat Cost anti
-- statement:
--   The Auto construction uses the mat Cost anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1947-L1950
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1947-L1950

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

theorem Auto.matCost_anti {P Q : Matrix n n ℂ} (hQ : Q.PosSemidef) (hPQ : P ≤ Q) (K : Matrix n n ℂ) :
    matCost Q K ≤ matCost P K := by sorry
