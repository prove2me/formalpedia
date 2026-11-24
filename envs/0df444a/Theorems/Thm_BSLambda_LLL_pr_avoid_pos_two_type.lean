-- Prove2me | Theorems.Thm_BSLambda_LLL_pr_avoid_pos_two_type
-- name    : BSLambda.LLL.pr_avoid_pos_two_type
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:53:57.594234+00:00
-- url     : https://prove2.me/theorems/5a8ced16-14a9-4f69-8779-c2f95af83449
-- title:
--   LLL: pr avoid pos two type
-- statement:
--   The two-type asymmetric local lemma of Section 10.2 of `bs_lambda.txt`.  Each event has a
--   type `ty i : Bool`, and events of type `t` have probability at most `p t` and at most `D t s`
--   neighbours of type `s`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L248-L277
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L248-L277

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

theorem BSLambda.LLL.pr_avoid_pos_two_type (Ev : I → Finset (Cfg β)) (supp : I → Finset A)
    (hdet : ∀ i, Determined (supp i) (Ev i)) (ty : I → Bool)
    (p x : Bool → ℝ) (D : Bool → Bool → ℕ)
    (hp : ∀ i, pr (Ev i) ≤ p (ty i))
    (hD : ∀ i t, ((nbr supp i).filter fun j ↦ ty j = t).card ≤ D (ty i) t)
    (hx0 : ∀ t, 0 < x t) (hx1 : ∀ t, x t < 1)
    (hcond : ∀ t, p t ≤ x t * (1 - x false) ^ D t false * (1 - x true) ^ D t true) :
    0 < pr (Finset.univ.filter fun ω ↦ ∀ i, ω ∉ Ev i) := by sorry
