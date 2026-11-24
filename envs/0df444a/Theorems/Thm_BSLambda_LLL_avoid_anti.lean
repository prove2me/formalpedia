-- Prove2me | Theorems.Thm_BSLambda_LLL_avoid_anti
-- name    : BSLambda.LLL.avoid_anti
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:53:53.581788+00:00
-- url     : https://prove2.me/theorems/6518fcf4-8bb4-4c6a-ae45-c7f7f7c2715b
-- title:
--   LLL: avoid anti
-- statement:
--   Avoiding more events is a smaller event.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L92-L94
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L92-L94

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)] [∀ a, Nonempty (β a)]
variable {I : Type*} [Fintype I] [DecidableEq I]
omit [∀ (a : A), Nonempty (β a)]

theorem BSLambda.LLL.avoid_anti {Ev : I → Finset (Cfg β)} {S T : Finset I} (h : S ⊆ T) :
    avoid Ev T ⊆ avoid Ev S := by sorry
