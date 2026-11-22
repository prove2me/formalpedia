-- Prove2me | Theorems.Thm_Auto_emb2_isometry
-- name    : Auto.emb2_isometry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:43:08.976374+00:00
-- url     : https://prove2.me/theorems/ecbcc477-7542-41f9-959e-26fc3008916b
-- title:
--   Auto: emb2 isometry
-- statement:
--   The Auto construction uses the emb2 isometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2428-L2436
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2428-L2436

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

theorem Auto.emb2_isometry {p r : Fin 3} (hpr : p ≠ r) : (emb2 (ι := ι) p r)ᴴ * emb2 (ι := ι) p r = 1 := by sorry
