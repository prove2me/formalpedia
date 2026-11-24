-- Prove2me | Theorems.Thm_BSLambda_LLL_pr_coord_mem
-- name    : BSLambda.LLL.pr_coord_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:53:40.312191+00:00
-- url     : https://prove2.me/theorems/007e0827-7959-440e-817b-cf4f2be87aeb
-- title:
--   LLL: pr coord mem
-- statement:
--   A single coordinate lands in a prescribed set with probability `|s| / |β a|`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L261-L273
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L261-L273

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

theorem BSLambda.LLL.pr_coord_mem (a : A) (s : Finset (β a)) :
    pr (Finset.univ.filter fun ω : Cfg β => ω a ∈ s)
      = (s.card : ℝ) / (Fintype.card (β a) : ℝ) := by sorry
