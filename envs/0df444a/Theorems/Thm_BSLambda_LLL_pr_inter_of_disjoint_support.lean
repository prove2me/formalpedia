-- Prove2me | Theorems.Thm_BSLambda_LLL_pr_inter_of_disjoint_support
-- name    : BSLambda.LLL.pr_inter_of_disjoint_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:49:33.742935+00:00
-- url     : https://prove2.me/theorems/b04ad199-efcb-4708-9e35-2928557aea67
-- title:
--   LLL: pr inter of disjoint support
-- statement:
--   **Independence.**  Two events determined by disjoint sets of coordinates are independent
--   for the uniform counting probability.  This is the probabilistic input to the local lemma of
--   Section 10 of `bs_lambda.txt`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L217-L234
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L217-L234

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
variable [∀ a, Nonempty (β a)]

theorem BSLambda.LLL.pr_inter_of_disjoint_support {S T : Finset A} {E F : Finset (Cfg β)}
    (hE : Determined S E) (hF : Determined T F) (hST : Disjoint S T) :
    pr (E ∩ F) = pr E * pr F := by sorry
