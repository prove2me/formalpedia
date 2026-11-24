-- Prove2me | Theorems.Thm_BSLambda_LLL_Determined_mem_glue_iff_left
-- name    : BSLambda.LLL.Determined.mem_glue_iff_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:53:27.569578+00:00
-- url     : https://prove2.me/theorems/4a478191-73e2-407e-a606-9d53884a014e
-- title:
--   Determined: mem glue iff left
-- statement:
--   An event determined by `S` only sees the `S`-half of a glued configuration.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L190-L192
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L190-L192

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

theorem BSLambda.LLL.Determined.mem_glue_iff_left {S : Finset A} {E : Finset (Cfg β)} (hE : Determined S E)
    {u v : Cfg β} : glue S u v ∈ E ↔ u ∈ E := by sorry
