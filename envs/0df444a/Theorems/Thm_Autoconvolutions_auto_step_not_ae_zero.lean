-- Prove2me | Theorems.Thm_Autoconvolutions_auto_step_not_ae_zero
-- name    : Autoconvolutions.auto_step_not_ae_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:08.683826+00:00
-- url     : https://prove2.me/theorems/0e40f9e9-7fd7-4474-8454-55c784c20635
-- title:
--   Autoconvolutions: auto step not ae zero
-- statement:
--   The Autoconvolutions construction uses the auto step not ae zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Step.lean#L60-L65
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Step.lean#L60-L65

module
public import Definitions.Def_Autoconvolutions_Definitions
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Convolution
public import Definitions.Def_Autoconvolutions_Step
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped ENNReal BigOperators
open Autoconvolutions

theorem Autoconvolutions.auto_step_not_ae_zero {d : ℕ} {p : Fin (d + 1) → ℝ}
    (hp : ∀ j, 0 ≤ p j) (hne : ∃ j, 0 < p j) : ¬ auto (step d p) =ᵐ[volume] 0 := by sorry
