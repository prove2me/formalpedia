-- Prove2me | Theorems.Thm_AnalystRank_Informativeness_claim_1_B1
-- name    : AnalystRank.Informativeness.claim_1_B1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:06.272321+00:00
-- url     : https://prove2.me/theorems/4ac80302-aa31-499e-8982-a5e2b00c7899
-- title:
--   Claim 1 (A), (B.1) — truthful forecasting against (1, 1): ΔUʰ ≥ 0 iff q ≥ 1 − q_min and ΔUˡ ≥ 0 iff q ≤ q_min, q_min ∈ (0, 1)
-- statement:
--   Let $\gamma\in(\tfrac12,1)$, $\rho\in[0,1]$ and $w_1>w_0>w_2$, with payoff convexity $\varphi=(w_1-w_0)/(w_0-w_2)$ and $\chi=\rho\gamma(1-\gamma)$. Put
--
--   $$q_{\min}=\gamma-\chi\,\frac{\varphi-1}{(1-\gamma)\varphi+\gamma}.$$
--
--   Then:
--
--   1. if $\rho=0$, then $q_{\min}=\gamma$ (Part (A));
--   2. $q_{\min}\in(0,1)$;
--   3. for every prior $q\in(0,1)$, when the other analyst forecasts truthfully ($\sigma=(1,1)$), the net payoffs of a truthful forecast in the rank game satisfy
--   $$\Delta U^h(1,1,q)\ge 0\iff q\ge 1-q_{\min},\qquad \Delta U^l(1,1,q)\ge0\iff q\le q_{\min}.$$
--
--   So the separating profile $(1,1)$ is an equilibrium of the rank game exactly for $q\in[1-q_{\min},q_{\min}]$.
--
--   **Formalization Note** The printed claim states only the "if" directions. The proof (B.7) simplifies $\Delta U^l(1,1,q)\ge0$ to the equivalent $q\le q_{\min}$, and the goal needs the converse: $(1,1)$ is not an equilibrium for $q>q_{\min}$. The statement covers every $\rho\in[0,1]$ and every $\varphi>0$, including $\rho=0$, where $q_{\min}=\gamma$.
-- source:
--   Banerjee, Does Competition Improve Analysts’ Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (13 Nov 2017), pp. 33–35, Claim 1 (A), (B.1), (B.2) and proof (B.7)

import Mathlib
import Definitions.Def_AnalystRank_Informativeness_Model

namespace AnalystRank.Informativeness

open Set

theorem claim_1_B1 (γ ρ w1 w0 w2 : ℝ) (hγ0 : 1 / 2 < γ) (hγ1 : γ < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hw1 : w0 < w1) (hw2 : w2 < w0) :
    (ρ = 0 → qmin γ ρ (phi w1 w0 w2) = γ) ∧
    0 < qmin γ ρ (phi w1 w0 w2) ∧ qmin γ ρ (phi w1 w0 w2) < 1 ∧
    ∀ q ∈ Ioo (0 : ℝ) 1,
      (0 ≤ dU (rankPay w1 w0 w2) q γ ρ (1, 1) true ↔ 1 - qmin γ ρ (phi w1 w0 w2) ≤ q) ∧
      (0 ≤ dU (rankPay w1 w0 w2) q γ ρ (1, 1) false ↔ q ≤ qmin γ ρ (phi w1 w0 w2)) := by sorry

end AnalystRank.Informativeness
