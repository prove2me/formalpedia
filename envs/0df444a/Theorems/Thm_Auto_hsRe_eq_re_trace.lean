-- Prove2me | Theorems.Thm_Auto_hsRe_eq_re_trace
-- name    : Auto.hsRe_eq_re_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:26:56.308937+00:00
-- url     : https://prove2.me/theorems/0910cee7-2120-4e82-b7c6-8964ad0a0612
-- title:
--   Auto: hs Re eq re trace
-- statement:
--   The Auto construction uses the hs Re eq re trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1729-L1729
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1729-L1729

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

theorem Auto.hsRe_eq_re_trace (X Y : Matrix n n ℂ) : hsRe X Y = ((Xᴴ * Y).trace).re := by sorry
