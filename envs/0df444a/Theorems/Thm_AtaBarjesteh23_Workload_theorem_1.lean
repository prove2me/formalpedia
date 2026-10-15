-- Prove2me | Theorems.Thm_AtaBarjesteh23_Workload_theorem_1
-- name    : AtaBarjesteh23.Workload.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:39.858272+00:00
-- url     : https://prove2.me/theorems/43600fd5-49f7-490e-9590-733fd859711b
-- title:
--   Theorem 1, p. 21 — the barrier policy at l_γ⋆, u_γ⋆ with drift (56) is optimal for the EWF with long-run average cost γ⋆
-- statement:
--   Assume the standing assumptions, and let $B$ be an $\mathbb F$-Brownian motion with drift $\mu$ and variance $\sigma^2$, started at $0$, on a filtered probability space. Let $\gamma^\star$, $l_{\gamma^\star}$, $u_{\gamma^\star}$ and $\theta(w)=\frac{m'H^{-1}m}{2}v(w)$ be the objects constructed in §6 (Corollary 1, (49), (54), (56)). Then:
--
--   1. **(average cost of the candidate)** every barrier policy $(L,U,\theta(W))$ with lower barrier $l_{\gamma^\star}$, upper barrier $u_{\gamma^\star}$ and drift $\theta(W(t))$ satisfies
--   $$\lim_{t\to\infty}\frac1t\,\mathbb E\Big[\int_0^tc(\theta(W(s)))\,ds+\int_0^th(W(s))\,ds+\kappa L(t)\Big]=\gamma^\star;$$
--   2. **(optimality)** every admissible control $(L,U,\theta)$ of the EWF satisfies
--   $$\limsup_{t\to\infty}\frac1t\,\mathbb E\Big[\int_0^tc(\theta(s))\,ds+\int_0^th(W(s))\,ds+\kappa L(t)\Big]\ \ge\ \gamma^\star. \tag{29}$$
--
--   Together, the two-barrier policy with state-dependent drift rate (56) attains the minimal long-run average cost $\gamma^\star$ of the equivalent workload formulation; this is the basis of the pricing, outsourcing and scheduling policy of §7.
--
--   **Formalization Note** The comparison class is every admissible control (progressively measurable drift), which is what the paper's proof treats and which contains the stationary Markov policies to which §6 restricts attention. "Has a long-run average cost of $\gamma^\star$" is stated as a limit, "optimal for (29)" as a lower bound on the limsup. Costs are in $[0,\infty]$, so a control with infinite expected cost is covered. The existence of a barrier policy with these data (a reflected diffusion) is presupposed by the paper and not asserted: part 1 quantifies over all such policies. $\gamma^\star$ and $v$ are the paper's constructions (via choice), not parameters.
-- source:
--   Ata and Barjesteh, An Approximate Analysis of Dynamic Pricing, Outsourcing, and Scheduling Policies for a Multiclass Make-to-Stock Queue in the Heavy Traffic Regime, accepted manuscript (SSRN 3464763; published in Operations Research 71(1):341–357, 2023, doi:10.1287/opre.2022.2361), p. 21, Theorem 1

import Mathlib
import Definitions.Def_AtaBarjesteh23_Workload_Setting
import Definitions.Def_AtaBarjesteh23_Workload_DriftBM
import Definitions.Def_AtaBarjesteh23_Workload_Control

open MeasureTheory Set Filter Topology

namespace AtaBarjesteh23.Workload

theorem theorem_1 (M : Model) (hM : M.Standing)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ mΩ) (B : ℝ → Ω → ℝ) (hB : IsDriftBM 𝔽 P B M.μ M.σ) :
    (∀ L U W : ℝ → Ω → ℝ,
      IsBarrierPolicy 𝔽 P B M.lStar M.uStar (fun t ω => M.thetaStar (W t ω)) L U W →
      Tendsto (fun t => M.avgCost P (fun t ω => M.thetaStar (W t ω)) L W t) atTop
        (𝓝 (ENNReal.ofReal M.gammaStar))) ∧
    (∀ θ L U W : ℝ → Ω → ℝ, IsAdmissible 𝔽 P B θ L U W →
      ENNReal.ofReal M.gammaStar ≤ limsup (fun t => M.avgCost P θ L W t) atTop) := by sorry

end AtaBarjesteh23.Workload
