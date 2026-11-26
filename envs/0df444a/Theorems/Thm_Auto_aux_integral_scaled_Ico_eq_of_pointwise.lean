-- Prove2me | Theorems.Thm_Auto_aux_integral_scaled_Ico_eq_of_pointwise
-- name    : Auto.aux_integral_scaled_Ico_eq_of_pointwise
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:39:13.820768+00:00
-- url     : https://prove2.me/theorems/114d390b-57e7-4f07-93fb-d33922facdba
-- title:
--   Auto: aux integral scaled Ico eq of pointwise
-- statement:
--   The scaled kernel may be replaced by any pointwise equal integrand on
--   its scale interval.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L402-L411
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L402-L411

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

theorem Auto.aux_integral_scaled_Ico_eq_of_pointwise {N : ℕ}
    (P Q : ℝ → ℝ) (hPQ : ∀ s, s ∈ Ico (0 : ℝ) N → P s = Q s) :
    ∫ s : ℝ, ((N : ℝ)⁻¹ * (Ico (0 : ℝ) N).indicator (fun _ ↦ (1 : ℝ)) s) *
        P s =
      (N : ℝ)⁻¹ * ∫ s in Ico (0 : ℝ) N, Q s := by sorry
