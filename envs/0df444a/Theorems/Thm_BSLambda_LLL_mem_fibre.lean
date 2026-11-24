-- Prove2me | Theorems.Thm_BSLambda_LLL_mem_fibre
-- name    : BSLambda.LLL.mem_fibre
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:47:16.747507+00:00
-- url     : https://prove2.me/theorems/113f071a-477f-40c1-964b-752d729f3952
-- title:
--   LLL: mem fibre
-- statement:
--   Membership in a fibre.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L293-L295
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L293-L295

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
variable {G : Finset A}
omit [∀ (a : A), Nonempty (β a)]

theorem BSLambda.LLL.mem_fibre {c : (a : A) → a ∈ G → β a} {ω : Cfg β} :
    ω ∈ fibre G c ↔ ∀ a, ∀ ha : a ∈ G, ω a = c a ha := by sorry
