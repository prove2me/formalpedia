-- Prove2me | Theorems.Thm_Auto_aux_memLp_orbit_comp
-- name    : Auto.aux_memLp_orbit_comp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T17:47:41.781513+00:00
-- url     : https://prove2.me/theorems/63852389-2367-4356-8d90-e1537132a2c3
-- title:
--   Auto: aux mem Lp orbit comp
-- statement:
--   Membership in `Lᵖ` is stable under joint forward orbits.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1173-L1179
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1173-L1179

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section

theorem Auto.aux_memLp_orbit_comp {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {n : ℕ} (S : ErgodicSystem X μ n) (k : Fin n → ℕ)
    {E : Type*} [TopologicalSpace E] [ContinuousENorm E]
    {F : X → E} {p : ℝ≥0∞} (hF : MemLp F p μ) :
    MemLp (F ∘ aux_orbit S.transformation k) p μ := by sorry
