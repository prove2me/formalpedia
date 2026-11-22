-- Prove2me | Theorems.Thm_Auto_re_trace_mul_eq_sum
-- name    : Auto.re_trace_mul_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:31:10.950095+00:00
-- url     : https://prove2.me/theorems/a05a105b-daf4-4e88-b704-1e7472d18974
-- title:
--   Auto: re trace mul eq sum
-- statement:
--   The Auto construction uses the re trace mul eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1663-L1669
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1663-L1669

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

theorem Auto.re_trace_mul_eq_sum (C B : Matrix n n ℂ) :
    ((C * B).trace).re = (∑ i, ∑ j, B i j * C j i).re := by sorry
