-- Prove2me | Theorems.Thm_BSLambda_LLL_Determined_mono
-- name    : BSLambda.LLL.Determined.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:12:36.266917+00:00
-- url     : https://prove2.me/theorems/43de3eb2-d64f-44e4-8f71-38bcedcd1e83
-- title:
--   Determined: mono
-- statement:
--   An event determined by `S` is determined by any larger coordinate set.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L132-L134
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Prob.lean#L132-L134

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
omit [Fintype A] [DecidableEq A] [(a : A) → Fintype (β a)] [(a : A) → DecidableEq (β a)]

theorem BSLambda.LLL.Determined.mono {S T : Finset A} {E : Finset (Cfg β)} (hST : S ⊆ T)
    (hE : Determined S E) : Determined T E := by sorry
