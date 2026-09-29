-- Prove2me | Theorems.Thm_FeinbergLiang_ACOE_discounted_sS_optimal
-- name    : FeinbergLiang.ACOE.discounted_sS_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T21:04:33.151979+00:00
-- url     : https://prove2.me/theorems/7126509f-aeff-4efa-80bc-6af9ab94129f
-- title:
--   Theorem 4.3 — for $\alpha\in(\alpha^*,1)$ an $(s_\alpha,S_\alpha)$ policy is optimal for the discounted cost
-- statement:
--   Consider the inventory control problem and a discount factor $\alpha\in[0,1)$ with $\alpha>\alpha^*$, where $\alpha^*=1+\lim_{x\to-\infty}h(x)/(\bar cx)$. Let
--   $$G_\alpha(x)=\bar cx+\mathbb E[h(x-D)]+\alpha\,\mathbb E[v_\alpha(x-D)].$$
--   Then:
--   1. $G_\alpha$ is real-valued and attains its minimum;
--   2. for every minimizer $S_\alpha$ of $G_\alpha$ (4.5), the set $\{x\le S_\alpha: G_\alpha(x)\le K+G_\alpha(S_\alpha)\}$ is bounded below. Let $s_\alpha$ be its infimum (4.6). Then the $(s_\alpha,S_\alpha)$ policy is optimal for the discount factor $\alpha$;
--   3. the stationary policy that coincides with the $(s_\alpha,S_\alpha)$ policy except that it also orders up to $S_\alpha$ at $x=s_\alpha$ is optimal for the discount factor $\alpha$ as well.
--
--   The paper cites this from Feinberg and Liang (2017a, Theorem 4.4(i) and Corollary 5.4). It supplies the discount-optimal thresholds whose limits give the average-cost optimal $(s^*,S^*)$ policy.
--
--   **Formalization Note.** $G_\alpha$ is extended-real valued by definition, and its finiteness is part of the conclusion. $\alpha^*$ is an extended real and may be $-\infty$. "Optimal for the discount factor $\alpha$" means $v^\phi_\alpha(x)=v_\alpha(x)$ for all $x$, where $v_\alpha$ is the infimum over all history-dependent randomized policies.
-- source:
--   Feinberg and Liang, On the optimality equation for average cost Markov decision processes and its validity for inventory control, Annals of Operations Research 317, 2022, p. 577, Theorem 4.3 (citing Feinberg and Liang 2017a, Theorem 4.4(i), Corollary 5.4), Eqs. (4.3), (4.5)-(4.7)

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_FeinbergLiang_ACOE_Inventory
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal

namespace FeinbergLiang.ACOE

/-- Theorem 4.3 (Feinberg–Liang 2022, p. 577, citing Feinberg and Liang 2017a, Theorem 4.4(i) and
Corollary 5.4). For a nonnegative discount factor `α ∈ (α*, 1)`, `G_α` of (4.3) is real-valued
and has a minimizer; for every minimizer `S_α` (4.5), with `s_α` defined by (4.6) (the defining
set is bounded below), the `(s_α, S_α)` policy and its variant that also orders at `x = s_α` are
both optimal for the discount factor `α`. -/
theorem discounted_sS_optimal (D : InventoryData) (α : ℝ) (hα : α ∈ Set.Ico (0 : ℝ) 1)
    (hαstar : alphaStar D < (α : EReal)) :
    (∀ x, Galpha D α x ≠ ⊤) ∧
    (∃ S : ℝ, ∀ x, Galpha D α S ≤ Galpha D α x) ∧
    ∀ S : ℝ, (∀ x, Galpha D α S ≤ Galpha D α x) →
      BddBelow {x : ℝ | x ≤ S ∧ Galpha D α x ≤ (D.K : EReal) + Galpha D α S} ∧
      IsDiscOptimal (inventoryMDP D)
        (Policy.ofStationary (sSPolicy (lowerThreshold (Galpha D α) D.K S) S)
          (measurable_sSPolicy _ _)) α ∧
      IsDiscOptimal (inventoryMDP D)
        (Policy.ofStationary (sSPolicyLe (lowerThreshold (Galpha D α) D.K S) S)
          (measurable_sSPolicyLe _ _)) α := by sorry

end FeinbergLiang.ACOE
