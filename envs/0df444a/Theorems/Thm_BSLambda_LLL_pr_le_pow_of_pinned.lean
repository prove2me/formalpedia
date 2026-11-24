-- Prove2me | Theorems.Thm_BSLambda_LLL_pr_le_pow_of_pinned
-- name    : BSLambda.LLL.pr_le_pow_of_pinned
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:51:09.165708+00:00
-- url     : https://prove2.me/theorems/aa75357c-0865-49ff-b7c3-5c3ed7d4f0d5
-- title:
--   LLL: pr le pow of pinned
-- statement:
--   The constant-alphabet form of `pr_le_prod_of_pinned`, as used in Sections 8.1 and 9.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L357-L366
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L357-L366

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
omit [∀ a, DecidableEq (β a)]

theorem BSLambda.LLL.pr_le_pow_of_pinned {G T : Finset A} (hGT : Disjoint G T) (N : ℕ)
    (hN : ∀ a ∈ T, Fintype.card (β a) = N)
    (tgt : ((a : A) → a ∈ G → β a) → (a : A) → Finset (β a)) (m : ℕ)
    (hm : ∀ c, ∀ a ∈ T, (tgt c a).card ≤ m) {E : Finset (Cfg β)}
    (hE : ∀ ω ∈ E, ∀ a ∈ T, ω a ∈ tgt (fun b _ ↦ ω b) a) :
    pr E ≤ ((m : ℝ) / N) ^ T.card := by sorry
