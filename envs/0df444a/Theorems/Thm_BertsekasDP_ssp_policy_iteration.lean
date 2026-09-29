-- Prove2me | Theorems.Thm_BertsekasDP_ssp_policy_iteration
-- name    : BertsekasDP.ssp_policy_iteration
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-08T00:44:13.802543+00:00
-- url     : https://prove2.me/theorems/d5f9d7b1-f748-49c8-a3e5-222a01053dbd
-- title:
--   Policy iteration (Prop. 7.2.2)
-- statement:
--   **Proposition 7.2.2 (policy iteration).** Under Assumption 7.2.1, consider policy iteration: starting from an admissible stationary policy $\mu^0$, alternately **evaluate** the current policy, solving $J_k = T_{\mu^k} J_k$, and **improve** it, choosing $\mu^{k+1}(i)$ to attain
--
--   $$\min_{u \in U(i)} \Bigl[\, g(i,u) + \sum_{j=1}^{n} p_{ij}(u) J_k(j) \,\Bigr] \qquad \text{for every } i .$$
--
--   Then the generated policies improve monotonically and the algorithm terminates with an optimal policy:
--
--   $$J_{k+1}(i) \;\le\; J_k(i) \quad \text{for all } i \text{ and } k, \qquad\text{and}\qquad J_k = T J_k \ \text{ for some } k .$$
--
--   Policy iteration is the alternative to value iteration that terminates **finitely** rather than in the limit: each iteration either strictly improves some state's cost or has already reached a solution of Bellman's equation, and there are only finitely many stationary policies. In practice it converges in very few iterations, at the price of solving a linear system per step.
--
--   **Formalization Note** The evaluations $J_k$ are given as fixed points of the corresponding policy operators, matching the linear system solved in practice. Reaching a $k$ with $T J_k = J_k$ is exactly optimality by Prop. 7.2.1(b),(d).
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Proposition 7.2.2

import Mathlib
import Definitions.Def_BertsekasSSPModel

namespace BertsekasDP

theorem ssp_policy_iteration {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C)
    (hA : ∃ m : ℕ, 0 < m ∧ ∀ π, BertsekasSSPAdmissible M π →
      ∀ i, BertsekasSSPSurvival M π m i < 1)
    (μ : ℕ → Fin n → C) (hadm : ∀ k i, μ k i ∈ M.U i)
    (J : ℕ → Fin n → ℝ)
    (heval : ∀ k, BertsekasSSPPolicyOp M (μ k) (J k) = J k)
    (himp : ∀ k i,
      M.g i (μ (k + 1) i) + ∑ j, M.p i (μ (k + 1) i) j * J k j =
        BertsekasSSPBellmanOp M (J k) i) :
    (∀ k i, J (k + 1) i ≤ J k i) ∧
    (∃ k, BertsekasSSPBellmanOp M (J k) = J k) := by sorry

end BertsekasDP
