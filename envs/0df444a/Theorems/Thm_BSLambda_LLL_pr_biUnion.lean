-- Prove2me | Theorems.Thm_BSLambda_LLL_pr_biUnion
-- name    : BSLambda.LLL.pr_biUnion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:51:00.54912+00:00
-- url     : https://prove2.me/theorems/1b55b39e-bb68-4cda-8939-528bcb12844c
-- title:
--   LLL: pr bi Union
-- statement:
--   **Finite additivity.**  The probability of a union of pairwise disjoint events is the sum
--   of the probabilities.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L91-L95
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L91-L95

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

theorem BSLambda.LLL.pr_biUnion {κ : Type*} {T : Finset κ} {E : κ → Finset (Cfg β)}
    (hdisj : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → Disjoint (E i) (E j)) :
    pr (T.biUnion E) = ∑ i ∈ T, pr (E i) := by sorry
