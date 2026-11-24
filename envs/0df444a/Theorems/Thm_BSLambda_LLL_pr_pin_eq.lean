-- Prove2me | Theorems.Thm_BSLambda_LLL_pr_pin_eq
-- name    : BSLambda.LLL.pr_pin_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:53:41.086581+00:00
-- url     : https://prove2.me/theorems/3f83a738-aabd-4cf1-ad24-7e3134866178
-- title:
--   LLL: pr pin eq
-- statement:
--   **Pinning several coordinates.**  Distinct coordinates are independent, so the
--   probability that each of them lands in a prescribed set is the product of the individual
--   probabilities.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L278-L291
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L278-L291

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

theorem BSLambda.LLL.pr_pin_eq (T : Finset A) (s : (a : A) → Finset (β a)) :
    pr (Finset.univ.filter fun ω : Cfg β => ∀ a ∈ T, ω a ∈ s a)
      = ∏ a ∈ T, ((s a).card : ℝ) / (Fintype.card (β a) : ℝ) := by sorry
