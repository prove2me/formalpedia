-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_step_sum_form_of_window_shift
-- name    : BooleanIsoperimetry.harper_step_sum_form_of_window_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:39:28.03028+00:00
-- url     : https://prove2.me/theorems/3a45afe6-890a-445c-8b93-c48ec52e22ef
-- title:
--   Boolean Isoperimetry: harper step sum form of window shift
-- statement:
--   The Boolean Isoperimetry construction uses the harper step sum form of window shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L166-L178
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L166-L178

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Harper
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry

theorem BooleanIsoperimetry.harper_step_sum_form_of_window_shift (n : ℕ)
    {a b p q : ℕ}
    (hap : a ≤ p) (hqb : q ≤ b)
    (hwin :
      gShiftIntervalCount (n + 1) a p ≤
        gShiftIntervalCount (n + 1) q b) :
    H (n + 1) p + H (n + 1) q ≤ H (n + 1) a + H (n + 1) b := by sorry
