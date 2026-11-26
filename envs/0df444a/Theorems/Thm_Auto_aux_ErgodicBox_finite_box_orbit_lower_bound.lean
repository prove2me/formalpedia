-- Prove2me | Theorems.Thm_Auto_aux_ErgodicBox_finite_box_orbit_lower_bound
-- name    : Auto.aux_ErgodicBox.finite_box_orbit_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:44:37.582693+00:00
-- url     : https://prove2.me/theorems/c5f8d61d-7c46-5823-a5ce-1ea5fa7137d9
-- title:
--   aux Ergodic Box: finite box orbit lower bound
-- statement:
--   Converts a pointwise finite-box lower bound into the integrated lower
--   bound required by the transference assembly step.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2725-L2747
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2725-L2747

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
open Auto.aux_ErgodicBox
open MeasureTheory Set
open scoped ENNReal BigOperators

theorem Auto.aux_ErgodicBox.finite_box_orbit_lower_bound
    {X κ : Type*} [MeasurableSpace X] {μ : Measure X}
    (B : Finset κ) (T : κ → X → X)
    (hT : ∀ k ∈ B, MeasurePreserving (T k) μ μ)
    {J : ℕ} (d : Fin J → X → ℝ)
    (hd : ∀ j, AEStronglyMeasurable (d j) μ)
    (D : X → ℝ≥0∞)
    (hpoint : ∀ x, ∑ j : Fin J, ∑ k ∈ B,
      ‖d j (T k x)‖ₑ ^ (2 : ℕ) ≤ D x) :
    (B.card : ℝ≥0∞) * ∑ j : Fin J, eLpNorm (d j) 2 μ ^ 2 ≤
      ∫⁻ x, D x ∂μ := by sorry
