-- Prove2me | Theorems.Thm_AtaBarjesteh23_Workload_proposition_2
-- name    : AtaBarjesteh23.Workload.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:44.637514+00:00
-- url     : https://prove2.me/theorems/dcc812a3-418a-47b8-8239-2273e98d6c90
-- title:
--   Proposition 2, p. 16 — a barrier policy whose (γ, f) solves (35)–(36) has long-run average cost γ
-- statement:
--   Fix the standing assumptions and an $\mathbb F$-Brownian motion $B$ with drift $\mu$ and variance $\sigma^2$ on a filtered probability space. Let $l<u$, let $\theta:\mathbb R\to\mathbb R$ be measurable, let $\gamma\in\mathbb R$ and $f\in C^2([l,u])$ satisfy
--   $$\tfrac12\sigma^2f''(w)+\mu f'(w)-\theta(w)f'(w)+c(\theta(w))+h(w)=\gamma,\quad w\in(l,u), \tag{35}$$
--   $$f'(l)=-\kappa,\qquad f'(u)=0. \tag{36}$$
--   Then every barrier policy $(L,U,\theta(W))$ with lower barrier $l$, upper barrier $u$ and drift $\theta(W(t))$ has
--   $$\lim_{t\to\infty}\frac1t\,\mathbb E\Big[\int_0^tc(\theta(W(s)))\,ds+\int_0^th(W(s))\,ds+\kappa L(t)\Big]=\gamma.$$
--
--   Proposition 2 computes the long-run average cost of a barrier policy from a solution of the ODE (35)–(36); it is the first half of the verification argument for Theorem 1.
--
--   **Formalization Note** The average is computed in $[0,\infty]$ and the limit is to $\max(\gamma,0)$ as an extended nonnegative real (the costs are nonnegative, so a barrier policy can only exist with $\gamma\ge0$). Derivatives of $f$ are taken within $[l,u]$. The statement quantifies over all barrier policies with the given data; it does not assert that one exists.
-- source:
--   Ata and Barjesteh, An Approximate Analysis of Dynamic Pricing, Outsourcing, and Scheduling Policies for a Multiclass Make-to-Stock Queue in the Heavy Traffic Regime, accepted manuscript (SSRN 3464763; published in Operations Research 71(1):341–357, 2023, doi:10.1287/opre.2022.2361), p. 16, Proposition 2, (35)–(36)

import Mathlib
import Definitions.Def_AtaBarjesteh23_Workload_Setting
import Definitions.Def_AtaBarjesteh23_Workload_DriftBM
import Definitions.Def_AtaBarjesteh23_Workload_Control

open MeasureTheory Set Filter Topology

namespace AtaBarjesteh23.Workload

theorem proposition_2 (M : Model) (hM : M.Standing)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ mΩ) (B : ℝ → Ω → ℝ) (hB : IsDriftBM 𝔽 P B M.μ M.σ)
    (l u γ : ℝ) (hlu : l < u) (θf : ℝ → ℝ) (hθf : Measurable θf) (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ 2 f (Icc l u))
    (h35 : ∀ w ∈ Ioo l u,
      M.σ ^ 2 / 2 * iteratedDerivWithin 2 f (Icc l u) w + M.μ * derivWithin f (Icc l u) w
        - θf w * derivWithin f (Icc l u) w + M.cost (θf w) + M.hcost w = γ)
    (h36 : derivWithin f (Icc l u) l = -M.kappa ∧ derivWithin f (Icc l u) u = 0)
    (L U W : ℝ → Ω → ℝ) (hpol : IsBarrierPolicy 𝔽 P B l u (fun t ω => θf (W t ω)) L U W) :
    Tendsto (fun t => M.avgCost P (fun t ω => θf (W t ω)) L W t) atTop
      (𝓝 (ENNReal.ofReal γ)) := by sorry

end AtaBarjesteh23.Workload
