-- Prove2me | Theorems.Thm_Autoconvolutions_blocks_energy_le
-- name    : Autoconvolutions.blocks_energy_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:17.565591+00:00
-- url     : https://prove2.me/theorems/5de7261f-e70d-43de-9594-8b88d6e285ed
-- title:
--   Autoconvolutions: blocks energy le
-- statement:
--   For block starts with distinct higher digits, distinctness of the unit cells
--   follows arithmetically. A block of width zero contributes zero.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Bounds.lean#L100-L154
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Bounds.lean#L100-L154

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

theorem Autoconvolutions.blocks_energy_le {ι : Type*} (d : ℕ) (p : Fin (d+1) → ℝ)
    (D : ℕ) (T : Finset ι) (code width : ι → ℕ) (height : ι → ℝ)
    (hinj : Set.InjOn code (↑T)) (hw : ∀ i ∈ T, width i ≤ D)
    (heq : ∀ i ∈ T, ∀ h ≤ width i, convCoeff d p ((D*code i+h : ℕ) : ℤ) = height i) :
    ∑ i ∈ T, (width i : ℝ)*(height i)^2 ≤ (eLpNorm (auto (step d p)) 2 volume).toReal^2 := by sorry
