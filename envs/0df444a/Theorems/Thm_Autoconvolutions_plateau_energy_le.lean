-- Prove2me | Theorems.Thm_Autoconvolutions_plateau_energy_le
-- name    : Autoconvolutions.plateau_energy_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:15.108729+00:00
-- url     : https://prove2.me/theorems/710bfe92-e92a-4586-852b-884e153a352a
-- title:
--   Autoconvolutions: plateau energy le
-- statement:
--   Summing over any finite set of unit cells on which two neighboring
--   coefficients agree gives a lower bound on the true squared L² norm.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Bounds.lean#L63-L96
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Bounds.lean#L63-L96

module
public import Definitions.Def_Autoconvolutions_Step
public import Definitions.Def_Autoconvolutions_Interpolation
public import Mathlib.MeasureTheory.Function.L2Space
public import Definitions.Def_Autoconvolutions_Bounds
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators
open Autoconvolutions

theorem Autoconvolutions.plateau_energy_le (d : ℕ) (p : Fin (d+1) → ℝ) (S : Finset ℤ)
    (H : ℤ → ℝ) (hl : ∀ k ∈ S, convCoeff d p k = H k)
    (hr : ∀ k ∈ S, convCoeff d p (k+1) = H k) :
    ∑ k ∈ S, (H k)^2 ≤ (eLpNorm (auto (step d p)) 2 volume).toReal ^ 2 := by sorry
