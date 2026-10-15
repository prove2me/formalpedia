-- Prove2me | Theorems.Thm_AccelVI_SafeAVI_residual_geometric
-- name    : AccelVI.SafeAVI.residual_geometric
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:21.913289+00:00
-- url     : https://prove2.me/theorems/c88ab3a5-4155-42ca-ab1e-669ae0047268
-- title:
--   Proof of Theorem 7.1, p. 14 — ‖v_s − T(v_s)‖∞ ≤ λ′^s ‖v₀ − T(v₀)‖∞ for every s ∈ ℕ
-- statement:
--   Let $(\mathbb S,\mathbb A,P,r,\lambda)$ be a valid finite MDP with a nonempty action set and Bellman operator $T$, let $\lambda'\in[\lambda,1)$ and $\alpha,\gamma>0$, and let $(v_s)_{s\ge0}$ be the iterates of Safe Accelerated Value Iteration (Algorithm 1) started at $v_0\in\mathbb R^{\mathbb S}$. Then for every $s\in\mathbb N$,
--
--   $$\|v_s - T(v_s)\|_\infty \le \lambda'^{\,s}\,\|v_0 - T(v_0)\|_\infty .$$
--
--   The Bellman residual of the safe scheme therefore decays geometrically at rate $\lambda'$, whichever mix of accelerated and value-iteration steps the test in Step 5 selects. Combined with the bound of the distance to $v^*$ by the residual, it yields the rate of Theorem 7.1.
--
--   **Formalization Note** $\|\cdot\|_\infty$ is Mathlib's sup norm on `S → ℝ`; $v_s$ is `savi M lam' α γ v0 s`.
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, p. 14, proof of Theorem 7.1, sentence beginning "Overall, we have proved by recursion"

import Mathlib
import Definitions.Def_AccelVI_SafeAVI_Setting

namespace AccelVI.SafeAVI
theorem residual_geometric {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A]
    (M : MDP S A) (hM : M.Valid) (lam' α γ : ℝ) (hlam' : M.lam ≤ lam') (hlam'1 : lam' < 1)
    (hα : 0 < α) (hγ : 0 < γ) (v0 : S → ℝ) (s : ℕ) :
    ‖savi M lam' α γ v0 s - bellman M (savi M lam' α γ v0 s)‖ ≤ lam' ^ s * ‖v0 - bellman M v0‖ := by sorry
end AccelVI.SafeAVI
