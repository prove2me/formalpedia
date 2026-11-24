-- Prove2me | Theorems.Thm_BSLambda_LLL_avoid_insert
-- name    : BSLambda.LLL.avoid_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:53:53.170771+00:00
-- url     : https://prove2.me/theorems/ef59db63-aca4-463a-8820-9502e5d9310f
-- title:
--   LLL: avoid insert
-- statement:
--   Peeling one event off `avoid`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L98-L101
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L98-L101

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

theorem BSLambda.LLL.avoid_insert (Ev : I → Finset (Cfg β)) (i : I) (S : Finset I) :
    avoid Ev (insert i S) = (Ev i)ᶜ ∩ avoid Ev S := by sorry
