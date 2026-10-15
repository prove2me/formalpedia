-- Prove2me | Theorems.Thm_AccelVI_SafeAVI_first_step_residual
-- name    : AccelVI.SafeAVI.first_step_residual
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:48.259038+00:00
-- url     : https://prove2.me/theorems/ab2c3a16-3151-4704-9672-c856d610d678
-- title:
--   Proof of Theorem 7.1, p. 13 — the case s = 1: ‖v₁ − T(v₁)‖∞ ≤ λ‖v₀ − T(v₀)‖∞ ≤ λ′‖v₀ − T(v₀)‖∞
-- statement:
--   Let $(\mathbb S,\mathbb A,P,r,\lambda)$ be a valid finite MDP with a nonempty action set and Bellman operator $T$, let $\lambda'\in[\lambda,1)$ and $\alpha,\gamma>0$, and let $(v_s)_{s\ge0}$ be the iterates of Safe Accelerated Value Iteration (Algorithm 1) started at $v_0$, so that $v_1 = T(v_0)$. Then
--
--   $$\|v_1 - T(v_1)\|_\infty \le \lambda\,\|v_0 - T(v_0)\|_\infty \le \lambda'\,\|v_0 - T(v_0)\|_\infty .$$
--
--   This is the base case $s=1$ of the induction in the proof of Theorem 7.1, which shows that the Bellman residual of the S-AVI iterates decays like $\lambda'^s$.
--
--   **Formalization Note** Both inequalities of the chain are stated, as a conjunction. $v_1$ is the iterate `savi M lam' α γ v0 1`, which is $T(v_0)$ by definition.
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, p. 13, proof of Theorem 7.1, second display

import Mathlib
import Definitions.Def_AccelVI_SafeAVI_Setting

namespace AccelVI.SafeAVI
theorem first_step_residual {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A]
    (M : MDP S A) (hM : M.Valid) (lam' α γ : ℝ) (hlam' : M.lam ≤ lam') (hlam'1 : lam' < 1)
    (hα : 0 < α) (hγ : 0 < γ) (v0 : S → ℝ) :
    ‖savi M lam' α γ v0 1 - bellman M (savi M lam' α γ v0 1)‖ ≤ M.lam * ‖v0 - bellman M v0‖ ∧
    M.lam * ‖v0 - bellman M v0‖ ≤ lam' * ‖v0 - bellman M v0‖ := by sorry
end AccelVI.SafeAVI
