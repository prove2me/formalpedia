-- Prove2me | Theorems.Thm_FactorRMDP_ValueIter_theorem_5_1
-- name    : FactorRMDP.ValueIter.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T19:33:58.931748+00:00
-- url     : https://prove2.me/theorems/ba68d1f0-271a-4529-91f5-6565c1eac450
-- title:
--   Theorem 5.1 — under r-rectangularity, VI-PI converges to v* = F(v*), z* = p₀ᵀv*, and its stopping rule yields an ε-optimal deterministic policy
-- statement:
--   Consider a robust MDP whose factor matrix uncertainty set is r-rectangular, $\mathcal W = \mathcal W^1\times\cdots\times\mathcal W^r$, and a discount factor $\lambda\in(0,1)$. Let $F$ be the operator
--
--   $$F(v)_s = \max_{a\in\mathbb A}\Big\{ r_{sa} + \lambda\sum_{i=1}^r u^i_{sa}\min_{w_i\in\mathcal W^i} w_i^\top v\Big\},$$
--
--   and let Algorithm VI-PI be $v^0 = 0$, $v^{k+1} = F(v^k)$. Put $\theta(\varepsilon) = \varepsilon(1-\lambda)(2\lambda)^{-1}$. Then:
--
--   1. $F$ has a unique fixed point $v^*$, and $p_0^\top v^*$ is the optimal value of the policy improvement problem: $z^* = \max_{\pi\in\Pi} z(\pi) = p_0^\top v^*$, the maximum being attained.
--   2. $v^k \to v^*$.
--   3. For every $\varepsilon>0$ and $k$, if $\|v^{k+1}-v^k\|_\infty < \theta(\varepsilon)$, then $\|v^{k+1}-v^*\|_\infty\le\varepsilon$, and every deterministic policy $d$ computed by VI-PI at that iteration, i.e. with $v^{k+1}_s = r_{s\,d(s)} + \lambda\sum_i u^i_{s\,d(s)}\min_{w_i\in\mathcal W^i}w_i^\top v^k$ for all $s$, is $\varepsilon$-optimal: $R(d,W)\ge z^*-\varepsilon$ for every $W\in\mathcal W$.
--   4. For every $\varepsilon>0$, if all rewards are at most $R_{\max}$ and $\lambda^k R_{\max} < \theta(\varepsilon)$, then $\|v^{k+1}-v^k\|_\infty<\theta(\varepsilon)$: the stopping test is passed after $O(\log \varepsilon^{-1})$ iterations.
--
--   So value iteration on $F$ returns an $\varepsilon$-optimal solution and an $\varepsilon$-optimal deterministic policy for the robust MDP problem.
--
--   **Formalization Note** The paper's count of arithmetic operations, $O\big(rSA\log\varepsilon^{-1} + \sum_i \mathrm{comp}(\mathcal W^i)\log^2\varepsilon^{-1}\big)$, counts calls to the optimization oracle of Assumption 2.4 and is not formalized; the iteration count is stated explicitly (item 4). The policy clause uses the policy VI-PI computes at iteration $k+1$ (greedy with respect to $v^k$). Norms on `S → ℝ` are sup norms. Rewards are nonnegative and $\mathbb A$ is nonempty (fields of the model).
-- source:
--   Goyal and Grand-Clément, Robust Markov Decision Process: Beyond Rectangularity, arXiv:1811.00215v8 (2021), p. 9, Theorem 5.1, (VI-PI); proof and running time, pp. 9–10

import Mathlib
import Definitions.Def_FactorRMDP_ValueIter_Model

namespace FactorRMDP.ValueIter

open Matrix Filter Topology

/-- Theorem 5.1 (Goyal and Grand-Clément, arXiv:1811.00215v8, pp. 9–10), by its mathematical
content. Let the uncertainty set be r-rectangular and let `v^k = F^k(0)` be the iterates of Algorithm
VI-PI. Then:
1. `F` has a unique fixed point `v*`, and `p₀ᵀv*` is the optimal value `z* = max_{π ∈ Π} z(π)` of
   the policy improvement problem (the maximum is attained);
2. `v^k → v*`;
3. (stopping rule, p. 10) for `ε > 0`, if `‖v^{k+1} − v^k‖_∞ < ε(1 − λ)(2λ)⁻¹` then
   `‖v^{k+1} − v*‖_∞ ≤ ε`, and every deterministic policy `d` computed by VI-PI at that iteration
   (an action attaining the maximum in the update `v^{k+1} = F(v^k)` at every state) is `ε`-optimal:
   `R(d, W) ≥ z* − ε` for every `W ∈ 𝒲`;
4. (iteration count) if every reward is at most `R_max` and `λ^k R_max < ε(1 − λ)(2λ)⁻¹`, the
   stopping test holds at iteration `k`; this is the explicit form of "after at most `O(log ε⁻¹)`
   iterations".
The paper's count of arithmetic operations (which counts calls to the oracle of Assumption 2.4) is not
formalized. -/
theorem theorem_5_1 {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    [Nonempty A] {r : ℕ} (M : Model S A r) (hR : M.IsRRect) {lam : ℝ} (hlam0 : 0 < lam)
    (hlam1 : lam < 1) :
    let v : ℕ → S → ℝ := fun k => M.viPI lam k
    let thr : ℝ → ℝ := fun ε => ε * (1 - lam) / (2 * lam)
    ∃ vstar : S → ℝ,
      M.F lam vstar = vstar ∧ (∀ w : S → ℝ, M.F lam w = w → w = vstar) ∧
      IsGreatest (M.z lam '' Policies S A) (M.p0 ⬝ᵥ vstar) ∧
      Tendsto v atTop (𝓝 vstar) ∧
      (∀ ε > 0, ∀ k : ℕ, ‖v (k + 1) - v k‖ < thr ε →
        ‖v (k + 1) - vstar‖ ≤ ε ∧
        ∀ d : S → A, (∀ s, v (k + 1) s =
            M.rew s (d s) + lam * ∑ i, M.u i s (d s) * M.minFactor i (v k)) →
          ∀ W ∈ M.Wset, M.p0 ⬝ᵥ vstar - ε ≤ M.R lam (fun s a => if a = d s then 1 else 0) W) ∧
      (∀ ε > 0, ∀ Rmax : ℝ, (∀ s a, M.rew s a ≤ Rmax) → ∀ k : ℕ, lam ^ k * Rmax < thr ε →
        ‖v (k + 1) - v k‖ < thr ε) := by sorry

end FactorRMDP.ValueIter
