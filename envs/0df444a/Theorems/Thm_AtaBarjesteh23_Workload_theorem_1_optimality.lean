-- Prove2me | Theorems.Thm_AtaBarjesteh23_Workload_theorem_1_optimality
-- name    : AtaBarjesteh23.Workload.theorem_1_optimality
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-23T20:47:20.104201+00:00
-- url     : https://prove2.me/theorems/15101ecb-89a9-41d3-a482-f368ee246e0c
-- title:
--   Theorem 1 (optimality claim), p. 21 — every admissible control of the EWF has long-run average cost ≥ γ⋆
-- statement:
--   Assume the standing assumptions and let $B$ be an $\mathbb F$-Brownian motion with drift $\mu$ and variance $\sigma^2$, started at $0$, on a filtered probability space. Let $\gamma^\star$ be the root constructed in Corollary 1 (the long-run average cost of the two-barrier policy of §6).
--
--   **Claim (optimality part of Theorem 1).** Every admissible control $(L,U,\theta)$ of the equivalent workload formulation, with workload $W(t) = B(t) - \int_0^t\theta(s)\,ds - U(t) + L(t)$ satisfying (30)–(32), has long-run average cost at least $\gamma^\star$:
--   $$\limsup_{t\to\infty}\frac1t\,\mathbb E\Big[\int_0^tc(\theta(s))\,ds+\int_0^th(W(s))\,ds+\kappa L(t)\Big]\ \ge\ \gamma^\star. \tag{29}$$
--
--   This is verbatim the second assertion of Theorem 1 (p. 21), split off so that the first assertion (the average cost of the barrier policy) can be reduced to Proposition 2 and Corollary 2. Costs are taken in $[0,\infty]$, so a control with infinite expected cost is covered; the comparison class is all admissible controls (progressively measurable drift), exactly as in the parent theorem `AtaBarjesteh23.Workload.theorem_1`. The paper's argument is a verification (Itô's formula) argument based on the solution $(l^\star,u^\star,\gamma^\star,f)$ of the Bellman equation (37)–(39) from Corollary 2.
-- source:
--   Ata and Barjesteh, An Approximate Analysis of Dynamic Pricing, Outsourcing, and Scheduling Policies for a Multiclass Make-to-Stock Queue in the Heavy Traffic Regime, accepted manuscript (SSRN 3464763; Operations Research 71(1):341–357, 2023, doi:10.1287/opre.2022.2361), p. 21, Theorem 1, second assertion (optimality, eq. (29))

import Mathlib
import Definitions.Def_AtaBarjesteh23_Workload_Setting
import Definitions.Def_AtaBarjesteh23_Workload_DriftBM
import Definitions.Def_AtaBarjesteh23_Workload_Control

open MeasureTheory Set Filter Topology

namespace AtaBarjesteh23.Workload

theorem theorem_1_optimality (M : Model) (hM : M.Standing)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ mΩ) (B : ℝ → Ω → ℝ) (hB : IsDriftBM 𝔽 P B M.μ M.σ) :
    ∀ θ L U W : ℝ → Ω → ℝ, IsAdmissible 𝔽 P B θ L U W →
      ENNReal.ofReal M.gammaStar ≤ limsup (fun t => M.avgCost P θ L W t) atTop := by sorry

end AtaBarjesteh23.Workload
