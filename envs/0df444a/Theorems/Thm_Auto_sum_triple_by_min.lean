-- Prove2me | Theorems.Thm_Auto_sum_triple_by_min
-- name    : Auto.sum_triple_by_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T18:42:43.686945+00:00
-- url     : https://prove2.me/theorems/fa8acbd2-3488-4089-868b-9a31b1c9243f
-- title:
--   Auto: sum triple by min
-- statement:
--   The Auto construction uses the sum triple by min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2072-L2120
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean#L2072-L2120

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

theorem Auto.sum_triple_by_min {κ : Type*} [LinearOrder κ] {M : Type*} [AddCommMonoid M]
    (f : κ → κ → κ → M) (hf : ∀ i j k, f i j k = f j k i) (s : Finset κ) :
    ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, f i j k = ∑ μ ∈ s, (3 • ∑ j ∈ s.filter (μ < ·), ∑ k ∈ s.filter (μ
      < ·), f μ j k + 3 • ∑ k ∈ s.filter (μ < ·), f μ μ k + f μ μ μ) := by sorry
