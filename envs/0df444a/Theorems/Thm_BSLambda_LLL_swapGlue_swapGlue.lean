-- Prove2me | Theorems.Thm_BSLambda_LLL_swapGlue_swapGlue
-- name    : BSLambda.LLL.swapGlue_swapGlue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:53:34.743684+00:00
-- url     : https://prove2.me/theorems/8e9b0e30-ad7b-4142-a3ed-b04a83eaba3c
-- title:
--   LLL: swap Glue swap Glue
-- statement:
--   `swapGlue S` is an involution.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L205-L208
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L205-L208

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
omit [Fintype A] [(a : A) → Fintype (β a)] [(a : A) → DecidableEq (β a)]

theorem BSLambda.LLL.swapGlue_swapGlue (S : Finset A) (p : Cfg β × Cfg β) :
    swapGlue S (swapGlue S p) = p := by sorry
