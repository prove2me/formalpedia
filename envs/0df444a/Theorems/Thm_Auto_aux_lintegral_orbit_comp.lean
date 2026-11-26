-- Prove2me | Theorems.Thm_Auto_aux_lintegral_orbit_comp
-- name    : Auto.aux_lintegral_orbit_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:47:16.349771+00:00
-- url     : https://prove2.me/theorems/4333f138-6429-4671-9ada-650fe7b0ebca
-- title:
--   Auto: aux lintegral orbit comp
-- statement:
--   A nonnegative measurable integral is invariant under a joint forward
--   orbit.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1157-L1161
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1157-L1161

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

theorem Auto.aux_lintegral_orbit_comp {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {n : ℕ} (S : ErgodicSystem X μ n) (k : Fin n → ℕ)
    {F : X → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F (aux_orbit S.transformation k x) ∂μ = ∫⁻ x, F x ∂μ := by sorry
