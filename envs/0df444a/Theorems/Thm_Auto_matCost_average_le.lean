-- Prove2me | Theorems.Thm_Auto_matCost_average_le
-- name    : Auto.matCost_average_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:42:24.427624+00:00
-- url     : https://prove2.me/theorems/57d2663d-9f95-4c4b-a73b-7c47eaca5282
-- title:
--   Auto: mat Cost average le
-- statement:
--   The Auto construction uses the mat Cost average le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1741-L1880
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1741-L1880

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

theorem Auto.matCost_average_le [IsProbabilityMeasure ν] {T K : Z → Matrix n n ℂ}
    (hTm : Measurable T) (hT : ∀ z, (T z).PosSemidef)
    (hTi : ∀ i j, Integrable (fun z => T z i j) ν)
    (hKi : ∀ i j, Integrable (fun z => K z i j) ν) :
    matCost (matIntegral ν T) (matIntegral ν K) ≤ ∫⁻ z, matCost (T z) (K z) ∂ν := by sorry
