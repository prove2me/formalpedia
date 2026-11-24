-- Prove2me | Theorems.Thm_BSLambda_LLL_pr_le_one
-- name    : BSLambda.LLL.pr_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:12:27.392167+00:00
-- url     : https://prove2.me/theorems/994276ce-027e-429e-927c-a969704b7d72
-- title:
--   LLL: pr le one
-- statement:
--   Probabilities are at most one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L74-L74
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L74-L74

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

theorem BSLambda.LLL.pr_le_one (E : Finset (Cfg β)) : pr E ≤ 1 := by sorry
