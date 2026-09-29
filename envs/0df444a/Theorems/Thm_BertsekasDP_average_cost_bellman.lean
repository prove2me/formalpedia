-- Prove2me | Theorems.Thm_BertsekasDP_average_cost_bellman
-- name    : BertsekasDP.average_cost_bellman
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-08T00:44:58.959771+00:00
-- url     : https://prove2.me/theorems/c8b41377-27bb-418b-a189-2b0450b2c3f8
-- title:
--   Average cost Bellman equation (Prop. 7.4.1)
-- statement:
--   **Proposition 7.4.1 (average cost per stage).** Consider the finite-state average-cost problem with stochastic transition rows, under **Assumption 7.4.1**: some designated state $s$ is visited within $m$ stages with positive probability, regardless of the policy and the initial state. Then there exist a scalar $\lambda^*$ and a vector $h^*$ with $h^*(s) = 0$ such that:
--
--   1. **Bellman's equation for the average-cost problem holds:**
--   $$\lambda^* + h^*(i) \;=\; \min_{u \in U(i)} \Bigl[\, g(i,u) + \sum_{j=1}^{n} p_{ij}(u) h^*(j) \,\Bigr], \qquad i = 1, \dots, n ;$$
--   2. **the gain is unique:** any pair $(\lambda, h)$ satisfying this equation has $\lambda = \lambda^*$;
--   3. **$\lambda^*$ is a lower bound on the average cost of every admissible policy:**
--   $$\lambda^* \;\le\; \liminf_{N \to \infty} \frac{1}{N} J^N_\pi(i) \qquad \text{for every admissible } \pi \text{ and every } i ;$$
--   4. **greedy stationary policies attain it:** if a stationary $\mu$ attains the minimum above for every $i$, then
--   $$\lim_{N \to \infty} \frac{1}{N} J^N_{\mu}(i) \;=\; \lambda^* \qquad \text{for every initial state } i .$$
--
--   The vector $h^*$ is a *differential* or *relative* cost: $h^*(i)$ measures the transient advantage of starting at $i$ rather than at the reference state $s$, once the long-run rate $\lambda^*$ has been accounted for. That the optimal average cost is the same from every initial state, and that it is determined by an equation of Bellman type, is what makes the average-cost criterion tractable at all.
--
--   **Formalization Note** Existence is asserted for the pair $(\lambda^*, h^*)$; only $\lambda^*$ is pinned down, as $h^*$ is determined only up to the normalization $h^*(s) = 0$ under this assumption. The lower bound is stated with $\liminf$ deliberately: for arbitrary nonstationary policies the Cesàro limit need not exist, while part 4 asserts a genuine limit for greedy stationary policies. The $N = 0$ term of the quotient is a junk value and does not affect the limit.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Proposition 7.4.1

import Mathlib
import Definitions.Def_BertsekasSSPModel

namespace BertsekasDP

theorem average_cost_bellman {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C)
    (hp1 : ∀ i, ∀ u ∈ M.U i, ∑ j, M.p i u j = 1)
    (s : Fin n)
    (hA : ∃ m : ℕ, 0 < m ∧ ∀ π, BertsekasSSPAdmissible M π →
      ∀ i, BertsekasSSPAvoidProb M s π m i < 1) :
    ∃ (lam : ℝ) (h : Fin n → ℝ),
      h s = 0 ∧
      (∀ i, lam + h i = BertsekasSSPBellmanOp M h i) ∧
      (∀ (lam' : ℝ) (h' : Fin n → ℝ),
        (∀ i, lam' + h' i = BertsekasSSPBellmanOp M h' i) → lam' = lam) ∧
      (∀ π, BertsekasSSPAdmissible M π → ∀ i,
        lam ≤ Filter.liminf
          (fun N => BertsekasSSPNCost M π N i / (N : ℝ)) Filter.atTop) ∧
      (∀ μ : Fin n → C, (∀ i, μ i ∈ M.U i) →
        (∀ i, lam + h i = M.g i (μ i) + ∑ j, M.p i (μ i) j * h j) →
        ∀ i, Filter.Tendsto
          (fun N => BertsekasSSPNCost M (fun _ => μ) N i / (N : ℝ))
          Filter.atTop (nhds lam)) := by sorry

end BertsekasDP
