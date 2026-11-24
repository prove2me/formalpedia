-- Prove2me | Theorems.Thm_BSLambda_LLL_pr_le_of_subset_biUnion
-- name    : BSLambda.LLL.pr_le_of_subset_biUnion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:49:26.77696+00:00
-- url     : https://prove2.me/theorems/7abbc983-3a51-455a-82c0-14b67f0ff39e
-- title:
--   LLL: pr le of subset bi Union
-- statement:
--   The union bound in the form used to cover an event by an enumeration of cases.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L118-L120
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L118-L120

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

theorem BSLambda.LLL.pr_le_of_subset_biUnion {κ : Type*} {E : Finset (Cfg β)}
    (T : Finset κ) (f : κ → Finset (Cfg β)) (h : E ⊆ T.biUnion f) :
    pr E ≤ ∑ i ∈ T, pr (f i) := by sorry
