-- Prove2me | Theorems.Thm_Auto_ofReal_integral_le_lintegral
-- name    : Auto.ofReal_integral_le_lintegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:41:47.626539+00:00
-- url     : https://prove2.me/theorems/da6d6e96-51c0-4b3b-bb36-ee63c0f5312f
-- title:
--   Auto: of Real integral le lintegral
-- statement:
--   The Auto construction uses the of Real integral le lintegral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1625-L1637
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L1625-L1637

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

theorem Auto.ofReal_integral_le_lintegral {f : Z → ℝ} (hf : Integrable f ν) :
    ENNReal.ofReal (∫ z, f z ∂ν) ≤ ∫⁻ z, ENNReal.ofReal (f z) ∂ν := by sorry
