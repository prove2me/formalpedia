-- Prove2me | Theorems.Thm_BSLambda_LLL_avoid_univ
-- name    : BSLambda.LLL.avoid_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:53:52.058406+00:00
-- url     : https://prove2.me/theorems/c11bb737-fb82-4c05-b0e3-eb8759dcc7df
-- title:
--   LLL: avoid univ
-- statement:
--   Avoiding every event is avoiding all of them.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L85-L88
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L85-L88

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

theorem BSLambda.LLL.avoid_univ (Ev : I → Finset (Cfg β)) :
    avoid Ev (Finset.univ : Finset I) = Finset.univ.filter fun ω ↦ ∀ i, ω ∉ Ev i := by sorry
