-- Prove2me | Theorems.Thm_BSLambda_LLL_disjoint_supp_sup_sdiff_nbr
-- name    : BSLambda.LLL.disjoint_supp_sup_sdiff_nbr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:53:45.678778+00:00
-- url     : https://prove2.me/theorems/158ab9b7-1577-4e5c-9a69-17249d5d20b3
-- title:
--   LLL: disjoint supp sup sdiff nbr
-- statement:
--   The events indexed outside the dependency neighbourhood of `i` are supported away from
--   `supp i`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L56-L62
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L56-L62

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

theorem BSLambda.LLL.disjoint_supp_sup_sdiff_nbr {supp : I → Finset A} {i : I} {S : Finset I} (hi : i ∉ S) :
    Disjoint (supp i) ((S \ nbr supp i).sup supp) := by sorry
