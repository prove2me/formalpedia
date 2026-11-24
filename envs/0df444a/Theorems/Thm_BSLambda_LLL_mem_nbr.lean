-- Prove2me | Theorems.Thm_BSLambda_LLL_mem_nbr
-- name    : BSLambda.LLL.mem_nbr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:46:55.234858+00:00
-- url     : https://prove2.me/theorems/a6a52d6e-b8ce-482a-ad42-c1f308986c95
-- title:
--   LLL: mem nbr
-- statement:
--   Membership in the dependency neighbourhood.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L49-L51
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L49-L51

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
omit [Fintype A]

theorem BSLambda.LLL.mem_nbr {supp : I → Finset A} {i j : I} :
    j ∈ nbr supp i ↔ j ≠ i ∧ ¬ Disjoint (supp i) (supp j) := by sorry
