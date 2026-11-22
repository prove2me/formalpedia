-- Prove2me | Theorems.Thm_Auto_hsRe_mul_right_eq
-- name    : Auto.hsRe_mul_right_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:42:22.044833+00:00
-- url     : https://prove2.me/theorems/ca0c1bad-c811-4c5b-9a74-379f4244cebd
-- title:
--   Auto: hs Re mul right eq
-- statement:
--   The Auto construction uses the hs Re mul right eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1737-L1739
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1737-L1739

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
variable {n : Type*} [Fintype n] [DecidableEq n] {Z : Type*} [MeasurableSpace Z] {ν : Measure Z}
omit [DecidableEq n]

theorem Auto.hsRe_mul_right_eq (A X : Matrix n n ℂ) :
    hsRe X (X * A) = (((Xᴴ * X) * A).trace).re := by sorry
