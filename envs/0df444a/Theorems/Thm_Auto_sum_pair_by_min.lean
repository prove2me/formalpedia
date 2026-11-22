-- Prove2me | Theorems.Thm_Auto_sum_pair_by_min
-- name    : Auto.sum_pair_by_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:42:43.135464+00:00
-- url     : https://prove2.me/theorems/81b69531-2f1f-4cce-8829-9842de47cc20
-- title:
--   Auto: sum pair by min
-- statement:
--   The Auto construction uses the sum pair by min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2122-L2153
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2122-L2153

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

theorem Auto.sum_pair_by_min {κ : Type*} [LinearOrder κ] {M : Type*} [AddCommMonoid M] (g : κ → κ → M)
    (s : Finset κ) :
    ∑ i ∈ s, ∑ j ∈ s, g i j = ∑ μ ∈ s, (g μ μ + ∑ j ∈ s.filter (μ < ·), (g μ j + g j μ)) := by sorry
