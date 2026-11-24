-- Prove2me | Theorems.Thm_BSLambda_LLL_mem_fibre_restrict
-- name    : BSLambda.LLL.mem_fibre_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:51:03.872047+00:00
-- url     : https://prove2.me/theorems/e6e8d3c1-1ebe-4d85-b17c-7f39dc8ee405
-- title:
--   LLL: mem fibre restrict
-- statement:
--   Every configuration lies in the fibre over its own restriction to `G`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L299-L300
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L299-L300

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

theorem BSLambda.LLL.mem_fibre_restrict (ω : Cfg β) : ω ∈ fibre G fun a _ ↦ ω a := by sorry
