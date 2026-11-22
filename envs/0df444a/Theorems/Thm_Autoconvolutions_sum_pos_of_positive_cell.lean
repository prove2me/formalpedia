-- Prove2me | Theorems.Thm_Autoconvolutions_sum_pos_of_positive_cell
-- name    : Autoconvolutions.sum_pos_of_positive_cell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:55.060539+00:00
-- url     : https://prove2.me/theorems/6735afa8-beff-4417-ae85-4b7b5cc63720
-- title:
--   Autoconvolutions: sum pos of positive cell
-- statement:
--   The Autoconvolutions construction uses the sum pos of positive cell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Step.lean#L42-L45
-- source:
--   https://github.com/VjekoKovac/lean-autoconvolutions/blob/e6a8e69129f67621693430dceeae42050377ffa6/Autoconvolutions/Step.lean#L42-L45

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

theorem Autoconvolutions.sum_pos_of_positive_cell {d : ℕ} {p : Fin (d + 1) → ℝ}
    (hp : ∀ j, 0 ≤ p j) (hne : ∃ j, 0 < p j) : 0 < ∑ j, p j := by sorry
