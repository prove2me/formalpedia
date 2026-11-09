-- Prove2me | Theorems.Thm_ApproxEquilibriumCost_General_lemma_2_2
-- name    : ApproxEquilibriumCost.General.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:02.103366+00:00
-- url     : https://prove2.me/theorems/60b66b28-fa37-412e-9cb7-9acbaa1a7b0d
-- title:
--   Lemma 2.2 — three equilibrium cross-cost implications
-- statement:
--   Let $G$ be any finite nonatomic congestion game with positive real population demands and continuous, nonnegative, nondecreasing latencies. Let $f,f'$ be feasible flows for the same demands, with resource loads $x,x'$, and let $\epsilon\ge0$. Then:
--
--   1. If $f$ is a Nash equilibrium, $C_f(f')-C(f)\ge0$.
--   2. If $f'$ is an $\epsilon$-equilibrium, $C(f')\le(1+\epsilon)C_{f'}(f)$.
--   3. If both equilibrium conditions hold,
--
--   $$\sum_e(x'_e-x_e)(\ell_e(x'_e)-\ell_e(x_e))\le\epsilon C_{f'}(f).$$
--
--   Each implication has its own equilibrium assumptions. No polynomial condition or positive-cost restriction is imposed. These comparisons connect the same flows evaluated at different induced latencies.
--
--   Differences from the source:
--   - encoding: arbitrary finite resource and population sets with subset strategies and real flows → Fin n and Fin k, with a bijective enumeration of all allowed population-strategy pairs; reason: every finite source instance is relabeled bijectively; empty subsets remain allowed and traffic remains real
--   - encoding: latencies defined on the nonnegative reals → total real functions constrained on [0,∞), evaluated only at nonnegative feasible loads; reason: values at negative arguments are unused, so the represented games are unchanged
-- source:
--   Yu Cheng, Tianle Jiang, STOC 2027 submission #438 (October 2026), How Much Can Approximate Equilibria Change the Social Cost of Selfish Routing?, Lemma 2.2 (Folklore), printed p.8 = PDF p.8 (offset 0). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/438.pdf

import Mathlib
import Definitions.Def_ApproxEquilibriumCost_General_FlowCosts

namespace ApproxEquilibriumCost.General

/-- Lemma 2.2 (Folklore), printed/PDF p.8. Each of the three implications
has its own equilibrium hypotheses; no polynomial or positive-cost restriction. -/
theorem lemma_2_2 {n k : ℕ} (G : Game n k) (f f' : Flow G)
    (hf : IsFeasible G f) (hf' : IsFeasible G f') (ε : ℝ) (hε : 0 ≤ ε) :
    (IsNash G f → 0 ≤ crossCost G f f' - cost G f) ∧
    (IsApproxNash G ε f' → cost G f' ≤ (1 + ε) * crossCost G f' f) ∧
    (IsNash G f → IsApproxNash G ε f' →
      (∑ e, (load G f' e - load G f e) *
        (G.latency e (load G f' e) - G.latency e (load G f e))) ≤
          ε * crossCost G f' f) := by sorry

end ApproxEquilibriumCost.General
