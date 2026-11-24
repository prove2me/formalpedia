-- Prove2me | Theorems.Thm_BSLambda_LLL_pr_coord_eq
-- name    : BSLambda.LLL.pr_coord_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:53:39.614527+00:00
-- url     : https://prove2.me/theorems/e2111dab-cc51-4022-a536-6b0f9d940505
-- title:
--   LLL: pr coord eq
-- statement:
--   A single coordinate takes a prescribed value with probability `1 / |β a|`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L254-L258
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L254-L258

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

theorem BSLambda.LLL.pr_coord_eq (a : A) (b : β a) :
    pr (Finset.univ.filter fun ω : Cfg β => ω a = b) = 1 / (Fintype.card (β a) : ℝ) := by sorry
