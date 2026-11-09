-- Prove2me | Theorems.Thm_ApproxEquilibriumCost_General_corollary_3_3
-- name    : ApproxEquilibriumCost.General.corollary_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:13.187781+00:00
-- url     : https://prove2.me/theorems/0a1bceb6-91dc-4995-a51c-e2b9aee5ff98
-- title:
--   Corollary 3.3 — exact lower bound for all approximate equilibria
-- statement:
--   Consider any finite nonatomic congestion game with positive real population demands, arbitrary nonempty families of resource-subset strategies, and polynomial resource latencies of degree at most an integer $d\ge1$ with nonnegative coefficients. Let $f$ be a Nash equilibrium with $C(f)>0$. For every real $\epsilon\ge0$ and every $\epsilon$-equilibrium $f'$ for the same game and demands,
--
--   $$\frac{C(f')}{C(f)}\ge1-\theta+\mu_d(\theta),\qquad\theta=\min\left\{\rho_d(\epsilon),\frac d{d+1}\right\}.$$
--
--   Here $\mu_d$ and $\rho_d$ are the functions of Definition 3.1. The bound includes $\epsilon=0$ and the entire saturation region; it asserts the displayed corollary without adding an attainment or sharpness clause from the subsequent examples.
--
--   Differences from the source:
--   - encoding: arbitrary finite resource and population sets with subset strategies and real flows → Fin n and Fin k, with a bijective enumeration of all allowed population-strategy pairs; reason: every finite source instance is relabeled bijectively; empty subsets remain allowed and traffic remains real
--   - encoding: latencies defined on the nonnegative reals → total real functions constrained on [0,∞), evaluated only at nonnegative feasible loads; reason: values at negative arguments are unused, so the represented games are unchanged
--   - encoding: integer d ≥ 1 and the power (1−x)^(1/d) → natural d with 1 ≤ d and Real.rpow with real reciprocal; reason: the admissible degrees and all endpoint values are identical
--   - encoding: ρ_d(ε) is the unique root of μ_d(u)=ε(1−u) in [0,1) → ρ_d(ε) is the infimum of {u∈[0,1] : ε(1−u)≤μ_d(u)}, with zero outside d≥1, ε≥0; reason: continuity and strict increase identify this nonempty bounded infimum with the unique source root; outside-domain defaults never enter a source-domain theorem
-- source:
--   Yu Cheng, Tianle Jiang, STOC 2027 submission #438 (October 2026), How Much Can Approximate Equilibria Change the Social Cost of Selfish Routing?, Corollary 3.3 (repeated/proved printed/PDF p.13), printed p.10 = PDF p.10 (offset 0). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/438.pdf

import Mathlib
import Definitions.Def_ApproxEquilibriumCost_General_FlowCosts
import Definitions.Def_ApproxEquilibriumCost_General_PolynomialLatencies
import Definitions.Def_ApproxEquilibriumCost_General_Parameters

namespace ApproxEquilibriumCost.General

/-- Corollary 3.3, printed/PDF p.10, repeated/proved p.13. Exact
all-degree, all-nonnegative-ε bound, including its saturation region. -/
theorem corollary_3_3 {n k : ℕ} (G : Game n k) (d : ℕ) (hd : 1 ≤ d)
    (hpoly : HasPolynomialLatencies G d) (f : Flow G)
    (hf : IsNash G f) (hcost : 0 < cost G f)
    (ε : ℝ) (hε : 0 ≤ ε) (f' : Flow G) (hf' : IsApproxNash G ε f') :
    let θ := min (rho d ε) (criticalPoint d)
    1 - θ + mu d θ ≤ cost G f' / cost G f := by sorry

end ApproxEquilibriumCost.General
