-- Prove2me | Theorems.Thm_FZEchelon_Discounted_theorem1_policy_optimal
-- name    : FZEchelon.Discounted.theorem1_policy_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:46:21.296101+00:00
-- url     : https://prove2.me/theorems/3584c93e-0346-4144-91f9-96639fc0c4a8
-- title:
--   Theorem 1, p. 827 — the decomposition policy $\pi_\alpha^*$ is optimal for the discounted problem $IH_\alpha$
-- statement:
--   Consider the one-depot, one-outlet inventory system of Federgruen and Zipkin. The cost factors $K, c^d, c^r, h^d, h^r, p^r$ are positive, the discount rate satisfies $0 \le \alpha < 1$, and the leadtimes $l, L$ are nonnegative integers. Demands in different periods are independent and identically distributed, nonnegative, continuous and of finite mean. Assume further the cost relation
--   $$
--   \alpha^l p^r \ge (1 - \alpha^l) h^d .
--   $$
--   Let $x^{r*}$ be a global minimizer of $(1-\alpha)c^r x + R(x)$, the critical number of the outlet problem. Let $\sigma^d$ be a measurable, nonnegative stationary order policy that is optimal for the depot problem $IH_\alpha^d$ (one-period cost $c^d(y) + D(v^d + y^L) + P(v^d + y^L)$) from every depot state with nonnegative outstanding orders. Let $\pi_\alpha^*$ be the stationary policy that orders $y = \sigma^d(\hat y, v^d)$ and ships
--   $$
--   z = \max\{0,\ \min\{x^{r*}, v^d + y^L\} - x^r\}.
--   $$
--
--   **Theorem.** $\pi_\alpha^*$ is a measurable stationary policy. From every physical state $s = (\hat y, v^d, x^r)$ ($\hat y \ge 0$, $x^r \le v^d$) it is admissible, and it is optimal for $IH_\alpha$: for every admissible policy $\pi$,
--   $$
--   B^\alpha(s \mid \pi_\alpha^*) \le B^\alpha(s \mid \pi),
--   $$
--   so $B^\alpha(s \mid \pi_\alpha^*) = B^\alpha(s) = \inf_\pi B^\alpha(s \mid \pi)$. Here $B^\alpha(s \mid \pi)$ is the expected total discounted cost of $\pi$ from $s$.
--
--   The theorem extends the Clark–Scarf decomposition to the infinite-horizon discounted problem. The system is optimally run by solving two single-location problems: a critical-number problem for the outlet, and a depot problem whose holding cost is augmented by the stationary induced penalty $P$. This penalty involves no optimal cost functions, so it can be computed directly.
--
--   **Formalization Note.** Admissible policies are measurable, non-anticipative, deterministic history-dependent rules, feasible along every demand path. The expected discounted cost is an extended real, the expectation of the positive part minus that of the negative part of the discounted cost sum. The cost relation is the condition named in the paper's proof of Theorem 1 (p. 827) as the one that "must hold"; the paper's §1 states only that the costs are related so that never ordering is not optimal. The optimality of $\sigma^d$ is the paper's definition of $\pi_\alpha^*$. No $(s, S)$ form is required.
-- source:
--   Federgruen and Zipkin, Computational Issues in an Infinite-Horizon, Multiechelon Inventory Model, Oper. Res. 32(4), 1984, p. 827, Theorem 1 (cost relation from its proof); π_α* defined on p. 825; shipment rule p. 819

import Mathlib
import Definitions.Def_FZEchelon_Discounted_Programs

open MeasureTheory Filter Topology

namespace FZEchelon.Discounted

/-- Theorem 1, p. 827: the policy `π_α*` (orders by an optimal stationary policy `σd` of the depot
problem `IH_α^d`, shipments up to `x^{r*}` as far as depot stock allows) is a measurable stationary
policy, admissible from every physical state, and optimal for `IH_α`: its expected discounted cost
is at most that of every admissible policy, from every physical state. -/
theorem theorem1_policy_optimal (M : Model) (hM : M.StandingAssumptions) (hα : M.α < 1)
    (hcost : (1 - M.α ^ M.l) * M.hd ≤ M.α ^ M.l * M.pr)
    (xstar : ℝ) (hx : M.IsStationaryCriticalNumber xstar)
    (σd : M.DepotState → ℝ) (hσm : Measurable σd) (hσnn : ∀ p, 0 ≤ σd p)
    (hσopt : ∀ p : M.DepotState, (∀ k, 0 ≤ p.1 k) → ∀ πd : Policy ℝ,
      (M.depotSystem xstar).Admissible πd p →
      (M.depotSystem xstar).discCost M.α M.ν ((M.depotSystem xstar).stationary σd p) p ≤
        (M.depotSystem xstar).discCost M.α M.ν πd p) :
    Measurable (M.piStar σd xstar) ∧
      ∀ s : M.State, M.InDomain s →
        M.system.Admissible (M.system.stationary (M.piStar σd xstar) s) s ∧
        ∀ π : Policy (ℝ × ℝ), M.system.Admissible π s →
          M.system.discCost M.α M.ν (M.system.stationary (M.piStar σd xstar) s) s ≤
            M.system.discCost M.α M.ν π s := by sorry

end FZEchelon.Discounted
