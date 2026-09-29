-- Prove2me | Theorems.Thm_BertsekasDP_ssp_main_theorem
-- name    : BertsekasDP.ssp_main_theorem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-08T00:42:30.610714+00:00
-- url     : https://prove2.me/theorems/3a724724-1a5e-4db7-a447-ad78a1e78244
-- title:
--   SSP main theorem (Prop. 7.2.1(a),(b) + optimality)
-- statement:
--   **Proposition 7.2.1(a),(b) (the stochastic shortest path theorem).** Consider the finite-state stochastic shortest path problem under **Assumption 7.2.1**: there is an integer $m > 0$ such that, regardless of the policy used and the initial state, termination is reached within $m$ stages with positive probability,
--
--   $$P\{x_m \ne t \mid x_0 = i, \pi\} \;<\; 1 \qquad \text{for every admissible } \pi \text{ and every state } i .$$
--
--   Then there is a cost vector $J^*$ such that:
--
--   1. **Value iteration converges from every start:** for any initial vector $J_0$,
--   $$\lim_{k \to \infty} (T^k J_0)(i) \;=\; J^*(i) \qquad \text{for every } i ;$$
--   2. **$J^*$ satisfies Bellman's equation and is its unique solution:**
--   $$J^*(i) \;=\; \min_{u \in U(i)} \Bigl[\, g(i,u) + \sum_{j=1}^{n} p_{ij}(u) J^*(j) \,\Bigr], \qquad i = 1,\dots,n ;$$
--   3. **$J^*$ is the optimal cost:** every admissible policy $\pi$ has a well-defined infinite-horizon cost $J_\pi(i) = \lim_N J^N_\pi(i)$ with $J^*(i) \le J_\pi(i)$, and some admissible **stationary** policy attains $J^*$.
--
--   This is the base case of infinite-horizon dynamic programming, and the theorem that value iteration and $Q$-learning ultimately rest on: the Bellman operator has a unique fixed point which is the optimal cost, and it can be found by iterating from anywhere. The discounted theory of §7.3 is the special case where termination occurs with probability $1-\alpha$ at each stage.
--
--   **Formalization Note** Uniqueness of the fixed point is asserted over all real-valued cost vectors, with no boundedness side condition. The existence of the limit defining $J_\pi$ for nonstationary policies is part of the claim, not an assumption. Assumption 7.2.1 is stated through the survival probability under admissible policies; the source notes one may always take $m = n$.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Proposition 7.2.1(a),(b)

import Mathlib
import Definitions.Def_BertsekasSSPModel

namespace BertsekasDP

theorem ssp_main_theorem {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C)
    (hA : ∃ m : ℕ, 0 < m ∧ ∀ π, BertsekasSSPAdmissible M π →
      ∀ i, BertsekasSSPSurvival M π m i < 1) :
    ∃ Jstar : Fin n → ℝ,
      (∀ J₀ : Fin n → ℝ,
        Filter.Tendsto (fun k => (BertsekasSSPBellmanOp M)^[k] J₀)
          Filter.atTop (nhds Jstar)) ∧
      BertsekasSSPBellmanOp M Jstar = Jstar ∧
      (∀ J : Fin n → ℝ, BertsekasSSPBellmanOp M J = J → J = Jstar) ∧
      (∀ π, BertsekasSSPAdmissible M π → ∀ i, ∃ Jπ : ℝ,
        Filter.Tendsto (fun N => BertsekasSSPNCost M π N i)
          Filter.atTop (nhds Jπ) ∧ Jstar i ≤ Jπ) ∧
      (∃ μ : Fin n → C, (∀ i, μ i ∈ M.U i) ∧ ∀ i,
        Filter.Tendsto (fun N => BertsekasSSPNCost M (fun _ => μ) N i)
          Filter.atTop (nhds (Jstar i))) := by sorry

end BertsekasDP
