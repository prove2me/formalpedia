-- Prove2me | Theorems.Thm_BSLambda_LLL_pr_eq_div
-- name    : BSLambda.LLL.pr_eq_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:48:45.571857+00:00
-- url     : https://prove2.me/theorems/95f7b575-dd5f-4c15-a598-4f75d32f2961
-- title:
--   LLL: pr eq div
-- statement:
--   `pr` as a quotient of cardinalities.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L57-L58
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L57-L58

module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob
set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)]
omit [(a : A) → DecidableEq (β a)]

theorem BSLambda.LLL.pr_eq_div (E : Finset (Cfg β)) :
    pr E = (E.card : ℝ) / (Fintype.card (Cfg β) : ℝ) := by sorry
