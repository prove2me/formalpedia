-- Prove2me | Theorems.Thm_Auto_matIntegral_posSemidef
-- name    : Auto.matIntegral_posSemidef
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:42:11.874853+00:00
-- url     : https://prove2.me/theorems/061ff2b0-0ec4-409b-b9ae-a97c9746093d
-- title:
--   Auto: mat Integral pos Semidef
-- statement:
--   The Auto construction uses the mat Integral pos Semidef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1691-L1726
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1691-L1726

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
omit [DecidableEq n] [Fintype n]

theorem Auto.matIntegral_posSemidef [Finite n] {M : Z → Matrix n n ℂ} (hM : ∀ z, (M z).PosSemidef)
    (hMi : ∀ i j, Integrable (fun z => M z i j) ν) :
    (matIntegral ν M).PosSemidef := by sorry
