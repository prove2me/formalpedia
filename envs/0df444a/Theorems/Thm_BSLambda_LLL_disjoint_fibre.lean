-- Prove2me | Theorems.Thm_BSLambda_LLL_disjoint_fibre
-- name    : BSLambda.LLL.disjoint_fibre
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:54:03.553839+00:00
-- url     : https://prove2.me/theorems/5547635f-6389-484c-be13-cb81871818fe
-- title:
--   LLL: disjoint fibre
-- statement:
--   Distinct partial configurations have disjoint fibres.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L310-L313
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L310-L313

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

theorem BSLambda.LLL.disjoint_fibre {c c' : (a : A) → a ∈ G → β a} (h : c ≠ c') :
    Disjoint (fibre G c) (fibre G c') := by sorry
