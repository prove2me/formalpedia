-- Prove2me | Theorems.Thm_ApproxEquilibriumCost_General_theorem_3_2
-- name    : ApproxEquilibriumCost.General.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:14.715547+00:00
-- url     : https://prove2.me/theorems/40a009f1-c205-45b8-a83a-21637cc3dad6
-- title:
--   Theorem 3.2 — unified polynomial bound for every admissible τ
-- statement:
--   Let $G$ be any nonatomic congestion game whose resource latencies are polynomials of degree at most an integer $d\ge1$ with nonnegative coefficients. Let $f$ be a Nash equilibrium with $C(f)>0$, and let $f'$ be an $\epsilon$-equilibrium for the same positive real population demands, where $\epsilon\ge0$. For every real $\tau\ge0$ satisfying
--
--   $$\frac{C(f)-C_{f'}(f)}{C(f)}\le\tau,$$
--
--   one has
--
--   $$\frac{C(f')}{C(f)}\ge1-\theta+\mu_d(\theta),\qquad\theta=\min\left\{\tau,\rho_d(\epsilon),\frac d{d+1}\right\}.$$
--
--   Positive Nash cost is the explicit standing assumption on p.8. All admissible $\tau$ are retained, including instances with nonpositive $C(f)-C_{f'}(f)$. This unified bound supplies the general congestion-game corollary.
--
--   Differences from the source:
--   - encoding: arbitrary finite resource and population sets with subset strategies and real flows → Fin n and Fin k, with a bijective enumeration of all allowed population-strategy pairs; reason: every finite source instance is relabeled bijectively; empty subsets remain allowed and traffic remains real
--   - encoding: latencies defined on the nonnegative reals → total real functions constrained on [0,∞), evaluated only at nonnegative feasible loads; reason: values at negative arguments are unused, so the represented games are unchanged
--   - encoding: integer d ≥ 1 and the power (1−x)^(1/d) → natural d with 1 ≤ d and Real.rpow with real reciprocal; reason: the admissible degrees and all endpoint values are identical
--   - encoding: ρ_d(ε) is the unique root of μ_d(u)=ε(1−u) in [0,1) → ρ_d(ε) is the infimum of {u∈[0,1] : ε(1−u)≤μ_d(u)}, with zero outside d≥1, ε≥0; reason: continuity and strict increase identify this nonempty bounded infimum with the unique source root; outside-domain defaults never enter a source-domain theorem
-- source:
--   Yu Cheng, Tianle Jiang, STOC 2027 submission #438 (October 2026), How Much Can Approximate Equilibria Change the Social Cost of Selfish Routing?, Theorem 3.2 (proof printed/PDF pp.11–13), printed p.10 = PDF p.10 (offset 0). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/438.pdf

import Mathlib
import Definitions.Def_ApproxEquilibriumCost_General_FlowCosts
import Definitions.Def_ApproxEquilibriumCost_General_PolynomialLatencies
import Definitions.Def_ApproxEquilibriumCost_General_Parameters

namespace ApproxEquilibriumCost.General

/-- Theorem 3.2, printed/PDF p.10, proof pp.11–13; positive Nash cost
is the explicit standing assumption on p.8. Every admissible τ is retained. -/
theorem theorem_3_2 {n k : ℕ} (G : Game n k) (d : ℕ) (hd : 1 ≤ d)
    (hpoly : HasPolynomialLatencies G d) (f f' : Flow G)
    (hf : IsNash G f) (hcost : 0 < cost G f)
    (ε : ℝ) (hε : 0 ≤ ε) (hf' : IsApproxNash G ε f')
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hgap : (cost G f - crossCost G f' f) / cost G f ≤ τ) :
    let θ := min τ (min (rho d ε) (criticalPoint d))
    1 - θ + mu d θ ≤ cost G f' / cost G f := by sorry

end ApproxEquilibriumCost.General
