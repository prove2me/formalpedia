-- Prove2me | Theorems.Thm_BSLambda_LLL_mem_avoid
-- name    : BSLambda.LLL.mem_avoid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:46:55.572435+00:00
-- url     : https://prove2.me/theorems/c5e900b5-6ff5-4b47-a1f9-b4d41104f4ad
-- title:
--   LLL: mem avoid
-- statement:
--   Membership in `avoid`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L72-L74
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L72-L74

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

theorem BSLambda.LLL.mem_avoid {Ev : I → Finset (Cfg β)} {S : Finset I} {ω : Cfg β} :
    ω ∈ avoid Ev S ↔ ∀ i ∈ S, ω ∉ Ev i := by sorry
