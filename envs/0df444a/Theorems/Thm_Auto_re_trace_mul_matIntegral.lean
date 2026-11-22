-- Prove2me | Theorems.Thm_Auto_re_trace_mul_matIntegral
-- name    : Auto.re_trace_mul_matIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:42:01.442198+00:00
-- url     : https://prove2.me/theorems/1824a2ae-0f15-4274-b75b-b9522f4d7ed1
-- title:
--   Auto: re trace mul mat Integral
-- statement:
--   The Auto construction uses the re trace mul mat Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1672-L1680
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1672-L1680

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

theorem Auto.re_trace_mul_matIntegral {M : Z → Matrix n n ℂ}
    (hM : ∀ i j, Integrable (fun z => M z i j) ν) (C : Matrix n n ℂ) :
    ((C * matIntegral ν M).trace).re = ∫ z, ((C * M z).trace).re ∂ν := by sorry
