-- Prove2me | Theorems.Thm_BertsekasDP_average_cost_policy_iteration
-- name    : BertsekasDP.average_cost_policy_iteration
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-08T00:45:29.526106+00:00
-- url     : https://prove2.me/theorems/92b14a0b-825f-40fe-b7da-98e9f9169113
-- title:
--   Average-cost policy iteration (Prop. 7.4.2)
-- statement:
--   **Proposition 7.4.2 (policy iteration for the average-cost problem).** Under Assumption 7.4.1, consider policy iteration in its average-cost form: **evaluate** the current stationary policy $\mu^k$ by solving
--
--   $$\lambda_k + h_k(i) \;=\; g\bigl(i, \mu^k(i)\bigr) + \sum_{j=1}^{n} p_{ij}\bigl(\mu^k(i)\bigr) h_k(j), \qquad h_k(s) = 0,$$
--
--   and **improve** it by letting $\mu^{k+1}(i)$ attain $\min_{u \in U(i)} [\, g(i,u) + \sum_j p_{ij}(u) h_k(j) \,]$ at every state. Then each iteration makes irreversible progress:
--
--   1. **the gain never increases:** $\lambda_{k+1} \le \lambda_k$ for every $k$;
--   2. **when the gain is unchanged, the differential costs do not increase:** if $\lambda_{k+1} = \lambda_k$ then $h_{k+1}(i) \le h_k(i)$ for every state $i$;
--   3. **the algorithm terminates at a solution of Bellman's equation:** for some $k$,
--   $$\lambda_k + h_k(i) \;=\; \min_{u \in U(i)} \Bigl[\, g(i,u) + \sum_{j=1}^{n} p_{ij}(u) h_k(j) \Bigr] \qquad \text{for every } i .$$
--
--   The two-tier progress measure is what the average-cost setting requires: an iteration that fails to reduce the long-run rate must at least reduce the transient term, and since there are finitely many stationary policies, neither can happen indefinitely. By Prop. 7.4.1 the pair reached at termination certifies the optimal average cost, and the policies attaining it are optimal.
--
--   **Formalization Note** The evaluation equations and the normalization $h_k(s) = 0$ are given as hypotheses on the sequences $(\lambda_k, h_k)$, matching the linear system solved at each step in practice. Part 2 is a conditional statement, asserted only at iterations where the gain is unchanged, and the inequality is not strict.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Proposition 7.4.2

import Mathlib
import Definitions.Def_BertsekasSSPModel

namespace BertsekasDP

theorem average_cost_policy_iteration {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C)
    (hp1 : ∀ i, ∀ u ∈ M.U i, ∑ j, M.p i u j = 1)
    (s : Fin n)
    (hA : ∃ m : ℕ, 0 < m ∧ ∀ π, BertsekasSSPAdmissible M π →
      ∀ i, BertsekasSSPAvoidProb M s π m i < 1)
    (μ : ℕ → Fin n → C) (hadm : ∀ k i, μ k i ∈ M.U i)
    (lam : ℕ → ℝ) (h : ℕ → Fin n → ℝ)
    (heval : ∀ k i, lam k + h k i =
      M.g i (μ k i) + ∑ j, M.p i (μ k i) j * h k j)
    (hnorm : ∀ k, h k s = 0)
    (himp : ∀ k i,
      M.g i (μ (k + 1) i) + ∑ j, M.p i (μ (k + 1) i) j * h k j =
        BertsekasSSPBellmanOp M (h k) i) :
    (∀ k, lam (k + 1) ≤ lam k) ∧
    (∀ k, lam (k + 1) = lam k → ∀ i, h (k + 1) i ≤ h k i) ∧
    (∃ k, ∀ i, lam k + h k i = BertsekasSSPBellmanOp M (h k) i) := by sorry

end BertsekasDP
