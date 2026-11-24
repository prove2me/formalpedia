-- Prove2me | Theorems.Thm_BSLambda_LLL_pr_compl_inter
-- name    : BSLambda.LLL.pr_compl_inter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:53:23.456233+00:00
-- url     : https://prove2.me/theorems/bdb2bd61-d5bd-44bd-b2eb-d58b738c4696
-- title:
--   LLL: pr compl inter
-- statement:
--   The complementary form of `pr_inter_add_pr_compl_inter`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L104-L105
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L104-L105

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

theorem BSLambda.LLL.pr_compl_inter (E F : Finset (Cfg β)) : pr (Eᶜ ∩ F) = pr F - pr (E ∩ F) := by sorry
