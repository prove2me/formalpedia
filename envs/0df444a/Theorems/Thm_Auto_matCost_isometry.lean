-- Prove2me | Theorems.Thm_Auto_matCost_isometry
-- name    : Auto.matCost_isometry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:31:14.146138+00:00
-- url     : https://prove2.me/theorems/9e7932c8-6ef1-400d-9613-31a784dfd78f
-- title:
--   Auto: mat Cost isometry
-- statement:
--   The Auto construction uses the mat Cost isometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1952-L2066
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1952-L2066

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

theorem Auto.matCost_isometry {k : Type*} [Fintype k] [DecidableEq k] (E : Matrix k n ℂ)
    (hE : Eᴴ * E = 1) {T : Matrix n n ℂ} (hT : T.PosSemidef) (K : Matrix n n ℂ) :
    matCost (E * T * Eᴴ) (E * K * Eᴴ) = matCost T K := by sorry
