-- Prove2me | Theorems.Thm_BSLambda_LLL_pr_pos_iff
-- name    : BSLambda.LLL.pr_pos_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:53:13.870445+00:00
-- url     : https://prove2.me/theorems/a5b33383-f14c-4167-99ba-c9675ca789dd
-- title:
--   LLL: pr pos iff
-- statement:
--   An event has positive probability exactly when it is nonempty.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L67-L67
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L67-L67

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

theorem BSLambda.LLL.pr_pos_iff {E : Finset (Cfg β)} : 0 < pr E ↔ E.Nonempty := by sorry
