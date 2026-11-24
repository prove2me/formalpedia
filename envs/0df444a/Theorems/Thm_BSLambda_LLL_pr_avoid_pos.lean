-- Prove2me | Theorems.Thm_BSLambda_LLL_pr_avoid_pos
-- name    : BSLambda.LLL.pr_avoid_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:53:57.635423+00:00
-- url     : https://prove2.me/theorems/c8560e4b-f9b2-4f1b-897e-a4b48958ed75
-- title:
--   LLL: pr avoid pos
-- statement:
--   **The asymmetric Lovász local lemma** (Section 10.2 of `bs_lambda.txt`).  If each bad
--   event `Ev i` is determined by `supp i` and has probability at most
--   `x i * ∏ j ∈ nbr supp i, (1 - x j)` for some weights `x i ∈ (0, 1)`, then with positive
--   probability no bad event occurs.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L232-L237
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L232-L237

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
variable (Ev : I → Finset (Cfg β)) (supp : I → Finset A) (x : I → ℝ)

theorem BSLambda.LLL.pr_avoid_pos (hdet : ∀ i, Determined (supp i) (Ev i))
    (hx0 : ∀ i, 0 < x i) (hx1 : ∀ i, x i < 1)
    (hcond : ∀ i, pr (Ev i) ≤ x i * ∏ j ∈ nbr supp i, (1 - x j)) :
    0 < pr (Finset.univ.filter fun ω ↦ ∀ i, ω ∉ Ev i) := by sorry
