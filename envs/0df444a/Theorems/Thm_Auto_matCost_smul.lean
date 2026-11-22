-- Prove2me | Theorems.Thm_Auto_matCost_smul
-- name    : Auto.matCost_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:31:19.325885+00:00
-- url     : https://prove2.me/theorems/99df0253-365d-48fd-9a5e-6a77399572ba
-- title:
--   Auto: mat Cost smul
-- statement:
--   The Auto construction uses the mat Cost smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1897-L1911
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1897-L1911

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

theorem Auto.matCost_smul (P K : Matrix n n ℂ) {c : ℝ} (hc : c ≠ 0) :
    matCost P (c • K) = ENNReal.ofReal (c ^ 2) * matCost P K := by sorry
