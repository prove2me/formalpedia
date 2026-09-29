-- Prove2me | Theorems.Thm_BertsekasDP_discounted_main_theorem
-- name    : BertsekasDP.discounted_main_theorem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-08T00:44:36.3771+00:00
-- url     : https://prove2.me/theorems/6cec52dc-7d73-41f0-8a8b-89416cc62c86
-- title:
--   Discounted problems (Prop. 7.3.1)
-- statement:
--   **Proposition 7.3.1 (discounted problems).** Consider the finite-state $\alpha$-discounted problem, $0 < \alpha < 1$, with stochastic transition rows $\sum_j p_{ij}(u) = 1$ at admissible controls. Then there is a cost vector $J^*$ for which all of the following hold:
--
--   1. **Value iteration converges** to $J^*$ from every initial vector;
--   2. **Bellman's equation** holds and determines $J^*$ uniquely:
--   $$J^*(i) \;=\; \min_{u \in U(i)} \Bigl[\, g(i,u) + \alpha \sum_{j=1}^{n} p_{ij}(u) J^*(j) \,\Bigr], \qquad i = 1,\dots,n ;$$
--   3. **$J^*$ is optimal:** every admissible policy has a well-defined cost $\ge J^*$, and some stationary policy attains it;
--   4. **policy evaluation:** each admissible stationary $\mu$ has a unique cost vector $J_\mu$ with $J_\mu = T_\mu^\alpha J_\mu$, reached by value iteration under $\mu$;
--   5. **optimality condition:** $J_\mu = J^*$ if and only if $\mu$ attains the minimum in Bellman's equation at every state;
--   6. **policy iteration** generates an improving sequence of policies and terminates with an optimal one.
--
--   The discounted model is the workhorse of reinforcement learning, and its theory is entirely inherited: the source derives it by attaching to the discounted problem an associated stochastic shortest path problem in which the state terminates with probability $1 - \alpha$ at each stage, so that costs and value iterates coincide and Assumption 7.2.1 holds automatically.
--
--   **Formalization Note** The six parts are packaged as one statement so that they share the single existential witness $J^*$, mirroring how the source states parts (a)–(e). Convergence is in the product topology on $\mathbb{R}^n$, equivalently in any norm since $n$ is finite. Discounting appears only in the operators; the underlying model is the one of §7.2, with stochastic rows imposed as a hypothesis.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Proposition 7.3.1

import Mathlib
import Definitions.Def_BertsekasSSPModel

namespace BertsekasDP

theorem discounted_main_theorem {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (hp1 : ∀ i, ∀ u ∈ M.U i, ∑ j, M.p i u j = 1) :
    ∃ Jstar : Fin n → ℝ,
      (∀ J₀ : Fin n → ℝ,
        Filter.Tendsto (fun k => (BertsekasDiscountedBellmanOp M α)^[k] J₀)
          Filter.atTop (nhds Jstar)) ∧
      BertsekasDiscountedBellmanOp M α Jstar = Jstar ∧
      (∀ J : Fin n → ℝ, BertsekasDiscountedBellmanOp M α J = J → J = Jstar) ∧
      (∀ π, BertsekasSSPAdmissible M π → ∀ i, ∃ Jπ : ℝ,
        Filter.Tendsto (fun N => BertsekasDiscountedNCost M α π N i)
          Filter.atTop (nhds Jπ) ∧ Jstar i ≤ Jπ) ∧
      (∃ μ : Fin n → C, (∀ i, μ i ∈ M.U i) ∧ ∀ i,
        Filter.Tendsto (fun N => BertsekasDiscountedNCost M α (fun _ => μ) N i)
          Filter.atTop (nhds (Jstar i))) ∧
      (∀ μ : Fin n → C, (∀ i, μ i ∈ M.U i) →
        ∃ Jμ : Fin n → ℝ,
          BertsekasDiscountedPolicyOp M α μ Jμ = Jμ ∧
          (∀ J : Fin n → ℝ,
            BertsekasDiscountedPolicyOp M α μ J = J → J = Jμ) ∧
          (∀ J₀ : Fin n → ℝ,
            Filter.Tendsto (fun k => (BertsekasDiscountedPolicyOp M α μ)^[k] J₀)
              Filter.atTop (nhds Jμ)) ∧
          (Jμ = Jstar ↔
            ∀ i, M.g i (μ i) + α * ∑ j, M.p i (μ i) j * Jstar j =
              BertsekasDiscountedBellmanOp M α Jstar i)) ∧
      (∀ (μ : ℕ → Fin n → C) (J : ℕ → Fin n → ℝ),
        (∀ k i, μ k i ∈ M.U i) →
        (∀ k, BertsekasDiscountedPolicyOp M α (μ k) (J k) = J k) →
        (∀ k i, M.g i (μ (k + 1) i) +
            α * ∑ j, M.p i (μ (k + 1) i) j * J k j =
          BertsekasDiscountedBellmanOp M α (J k) i) →
        (∀ k i, J (k + 1) i ≤ J k i) ∧
          ∃ k, BertsekasDiscountedBellmanOp M α (J k) = J k) := by sorry

end BertsekasDP
