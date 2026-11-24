-- Prove2me | Theorems.Thm_BSLambda_LLL_sum_pr_fibre
-- name    : BSLambda.LLL.sum_pr_fibre
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:54:05.444081+00:00
-- url     : https://prove2.me/theorems/bc1930ac-e428-4e94-b3cf-55c3847d45c6
-- title:
--   LLL: sum pr fibre
-- statement:
--   The fibres over `G` partition the configuration space, so their probabilities sum to `1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L316-L322
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L316-L322

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

theorem BSLambda.LLL.sum_pr_fibre (G : Finset A) :
    ∑ c ∈ G.pi fun a ↦ (Finset.univ : Finset (β a)), pr (fibre G c) = 1 := by sorry
