-- Prove2me | Theorems.Thm_Auto_re_sum_matIntegral_mul
-- name    : Auto.re_sum_matIntegral_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:41:57.817118+00:00
-- url     : https://prove2.me/theorems/51a5ea4d-d76f-4648-95a1-18f9dbf8f5c1
-- title:
--   Auto: re sum mat Integral mul
-- statement:
--   The Auto construction uses the re sum mat Integral mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1646-L1660
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1646-L1660

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

theorem Auto.re_sum_matIntegral_mul {M : Z → Matrix n n ℂ}
    (hM : ∀ i j, Integrable (fun z => M z i j) ν) (C : Matrix n n ℂ) :
    (∑ i, ∑ j, matIntegral ν M i j * C i j).re = ∫ z, (∑ i, ∑ j, M z i j * C i j).re ∂ν := by sorry
