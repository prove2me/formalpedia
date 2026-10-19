-- Prove2me | Theorems.Thm_AccelVI_SafeAVI_theorem_7_1
-- name    : AccelVI.SafeAVI.theorem_7_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:12.593923+00:00
-- url     : https://prove2.me/theorems/7922b3f2-83fe-47c2-8e7e-3529122c59b9
-- title:
--   Theorem 7.1, p. 13 — Safe Accelerated Value Iteration converges to v*, with v_s = v* + O(λ′^s) for all s ≥ 0
-- statement:
--   Let $(\mathbb S,\mathbb A,P,r,\lambda)$ be a finite MDP with a nonempty action set, in which every $P_{ia}$ is a probability distribution over next states and $\lambda\in(0,1)$, let $T$ be its Bellman operator and $v^*$ its fixed point, $T(v^*) = v^*$ (the optimal value function). Let $\lambda'\in[\lambda,1)$, let $\alpha,\gamma>0$ be any step sizes, and let $(v_s)_{s\ge0}$ be the iterates of Safe Accelerated Value Iteration (Algorithm 1) from any $v_0\in\mathbb R^{\mathbb S}$. Then $(v_s)_{s\ge 0}$ converges to $v^*$, and there is a constant $C$ such that
--
--   $$\|v_s - v^*\|_\infty \le C\,\lambda'^{\,s} \qquad \text{for all } s\ge 0,$$
--
--   that is, $v_s = v^* + O(\lambda'^s)$ for all $s\ge0$.
--
--   S-AVI alternates accelerated value-iteration steps with plain value-iteration steps. The theorem says this safeguard restores the worst-case guarantee of value iteration: for $\lambda' = \lambda$ the rate matches that of value iteration, which by the lower bound of Theorem 6.3 cannot be improved by any first-order method on all MDPs, while larger $\lambda'$ admits more accelerated steps.
--
--   **Formalization Note** $\|\cdot\|_\infty$ is Mathlib's sup norm on `S → ℝ`. "$v_s = v^* + O(\lambda'^s)$, $\forall s\ge0$" is encoded as one constant $C$ valid for every $s$, and convergence as `Filter.Tendsto` to `nhds vstar`. $v^*$ enters as a vector with $T(v^*) = v^*$, which exists and is unique for a valid MDP since $T$ is a $\lambda$-contraction. The hypotheses $\alpha,\gamma>0$ are those of Algorithm 1; the constant $C$ is not specified, as in the paper.
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, p. 13, Theorem 7.1; Algorithm 1 and proof p. 14

import Mathlib
import Definitions.Def_AccelVI_SafeAVI_Setting

namespace AccelVI.SafeAVI
theorem theorem_7_1 {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A]
    (M : MDP S A) (hM : M.Valid) (lam' α γ : ℝ) (hlam' : M.lam ≤ lam') (hlam'1 : lam' < 1)
    (hα : 0 < α) (hγ : 0 < γ) (v0 vstar : S → ℝ) (hfix : bellman M vstar = vstar) :
    Filter.Tendsto (savi M lam' α γ v0) Filter.atTop (nhds vstar) ∧
    ∃ C : ℝ, ∀ s : ℕ, ‖savi M lam' α γ v0 s - vstar‖ ≤ C * lam' ^ s := by sorry
end AccelVI.SafeAVI
