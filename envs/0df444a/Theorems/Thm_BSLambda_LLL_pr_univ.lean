-- Prove2me | Theorems.Thm_BSLambda_LLL_pr_univ
-- name    : BSLambda.LLL.pr_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:44:49.704803+00:00
-- url     : https://prove2.me/theorems/67e436ce-5975-4145-a2cb-68748f0a118b
-- title:
--   LLL: pr univ
-- statement:
--   The whole space has probability one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L83-L83
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L83-L83

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
variable [∀ a, Nonempty (β a)]

theorem BSLambda.LLL.pr_univ : pr (Finset.univ : Finset (Cfg β)) = 1 := by sorry
