-- Prove2me | Theorems.Thm_BSLambda_LLL_pr_mono
-- name    : BSLambda.LLL.pr_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:50:56.372615+00:00
-- url     : https://prove2.me/theorems/316da7fa-5716-4758-b1a5-931de79ef29b
-- title:
--   LLL: pr mono
-- statement:
--   Probability is monotone in the event.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L70-L71
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L70-L71

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

theorem BSLambda.LLL.pr_mono {E F : Finset (Cfg β)} (h : E ⊆ F) : pr E ≤ pr F := by sorry
