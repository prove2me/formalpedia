-- Prove2me | Theorems.Thm_Autoconvolutions_ratio_ge_blocks
-- name    : Autoconvolutions.ratio_ge_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:27.536278+00:00
-- url     : https://prove2.me/theorems/8ee463b7-005d-44a8-8c71-4c2587f830d1
-- title:
--   Autoconvolutions: ratio ge blocks
-- statement:
--   The contribution of an injectively indexed family of blocks to the ratio.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Bounds.lean#L157-L168
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Bounds.lean#L157-L168

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

theorem Autoconvolutions.ratio_ge_blocks {ι : Type*} (d : ℕ) (p : Fin (d+1) → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hne : ∃ i, 0 < p i) (M : ℝ) (hM : 0 < M) (hb : ∀ k : ℤ, convCoeff d p k ≤ M)
    (D : ℕ) (T : Finset ι) (code width : ι → ℕ) (height : ι → ℝ)
    (hinj : Set.InjOn code (↑T)) (hw : ∀ i ∈ T, width i ≤ D)
    (heq : ∀ i ∈ T, ∀ h ≤ width i, convCoeff d p ((D*code i+h : ℕ) : ℤ) = height i) :
    (∑ i ∈ T, (width i : ℝ)*(height i)^2) / ((∑ j, p j)^2*M) ≤ ratio (step d p) := by sorry
