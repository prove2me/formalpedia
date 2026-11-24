-- Prove2me | Theorems.Thm_BSLambda_LLL_glue_apply_of_mem
-- name    : BSLambda.LLL.glue_apply_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:45:37.065988+00:00
-- url     : https://prove2.me/theorems/125d770d-c478-42b6-8905-9fea7aa7362a
-- title:
--   LLL: glue apply of mem
-- statement:
--   The LLL construction uses the glue apply of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L183-L184
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L183-L184

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

theorem BSLambda.LLL.glue_apply_of_mem {S : Finset A} {u v : Cfg β} {a : A} (ha : a ∈ S) :
    glue S u v a = u a := by sorry
