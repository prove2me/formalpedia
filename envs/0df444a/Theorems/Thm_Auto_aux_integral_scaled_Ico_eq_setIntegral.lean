-- Prove2me | Theorems.Thm_Auto_aux_integral_scaled_Ico_eq_setIntegral
-- name    : Auto.aux_integral_scaled_Ico_eq_setIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:38:56.956251+00:00
-- url     : https://prove2.me/theorems/99e3fa3e-28c6-56e4-a74e-755e57ceff71
-- title:
--   Auto: aux integral scaled Ico eq set Integral
-- statement:
--   A scaled half-open interval kernel converts a full integral into the
--   corresponding scale-interval integral.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L377-L396
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L377-L396

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

theorem Auto.aux_integral_scaled_Ico_eq_setIntegral {N : ℕ} (P : ℝ → ℝ) :
    ∫ s : ℝ, ((N : ℝ)⁻¹ * (Ico (0 : ℝ) N).indicator (fun _ ↦ (1 : ℝ)) s) *
        P s =
      (N : ℝ)⁻¹ * ∫ s in Ico (0 : ℝ) N, P s := by sorry
