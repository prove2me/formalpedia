-- Prove2me | Theorems.Thm_BSLambda_LLL_avoid_empty
-- name    : BSLambda.LLL.avoid_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:46:58.944519+00:00
-- url     : https://prove2.me/theorems/e1ae0d16-c420-492a-ac8d-b6e3bd807cdd
-- title:
--   LLL: avoid empty
-- statement:
--   Avoiding no events is the sure event.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L78-L81
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L78-L81

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

theorem BSLambda.LLL.avoid_empty (Ev : I → Finset (Cfg β)) :
    avoid Ev ∅ = (Finset.univ : Finset (Cfg β)) := by sorry
