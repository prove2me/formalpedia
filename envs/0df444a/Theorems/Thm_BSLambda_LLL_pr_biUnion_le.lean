-- Prove2me | Theorems.Thm_BSLambda_LLL_pr_biUnion_le
-- name    : BSLambda.LLL.pr_biUnion_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:51:02.45585+00:00
-- url     : https://prove2.me/theorems/3ea9d374-626a-4fe0-be16-73bb427b848b
-- title:
--   LLL: pr bi Union le
-- statement:
--   **The union bound.**  The probability of a finite union is at most the sum of the
--   probabilities.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L111-L115
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L111-L115

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

theorem BSLambda.LLL.pr_biUnion_le {κ : Type*} (T : Finset κ) (E : κ → Finset (Cfg β)) :
    pr (T.biUnion E) ≤ ∑ i ∈ T, pr (E i) := by sorry
