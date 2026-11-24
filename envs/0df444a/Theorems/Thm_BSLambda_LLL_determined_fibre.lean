-- Prove2me | Theorems.Thm_BSLambda_LLL_determined_fibre
-- name    : BSLambda.LLL.determined_fibre
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:54:00.088511+00:00
-- url     : https://prove2.me/theorems/ead739fe-bf1c-48af-a8e4-5ac5516b82af
-- title:
--   LLL: determined fibre
-- statement:
--   A fibre over `G` is determined by `G`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L304-L306
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L304-L306

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

theorem BSLambda.LLL.determined_fibre (c : (a : A) → a ∈ G → β a) : Determined G (fibre G c) := by sorry
