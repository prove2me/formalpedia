-- Prove2me | Theorems.Thm_AnalystRank_Informativeness_claim_7
-- name    : AnalystRank.Informativeness.claim_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:03.911919+00:00
-- url     : https://prove2.me/theorems/b724069b-4533-47f0-9b96-1f2ed6b8af95
-- title:
--   Claim 7 — on σʰ ≥ 1 − σˡ, forecast informativeness Π(σʰ, σˡ) is strictly increasing in σʰ and in σˡ
-- statement:
--   Let $q\in(0,1)$, $\gamma\in(\tfrac12,1)$ and $\rho\in[0,1]$, and let $\Pi(\sigma^h,\sigma^l)$ be the forecast informativeness of Definition 3. Then:
--
--   1. for every $\sigma^l\in[0,1]$, $\sigma^h\mapsto\Pi(\sigma^h,\sigma^l)$ is strictly increasing on $\{\sigma^h\in[0,1]:\sigma^h\ge1-\sigma^l\}$;
--   2. for every $\sigma^h\in[0,1]$, $\sigma^l\mapsto\Pi(\sigma^h,\sigma^l)$ is strictly increasing on $\{\sigma^l\in[0,1]:\sigma^l\ge1-\sigma^h\}$.
--
--   Forecasts that follow the signal more often reveal more about the state. This is the link between Definition 2's coordinatewise order of equilibria and the comparison of informativeness in Proposition 5.
--
--   **Formalization Note** The paper states $\partial\Pi/\partial\sigma^h>0$ and $\partial\Pi/\partial\sigma^l>0$ for $\sigma^h>1-\sigma^l$. The statement here is strict monotonicity on the region including the pooling boundary $\sigma^h=1-\sigma^l$, which follows by continuity of $\Pi$.
-- source:
--   Banerjee, Does Competition Improve Analysts’ Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (13 Nov 2017), p. 55, Claim 7

import Mathlib
import Definitions.Def_AnalystRank_Informativeness_Model

namespace AnalystRank.Informativeness

open Set

theorem claim_7 (q γ ρ : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (hγ0 : 1 / 2 < γ) (hγ1 : γ < 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (∀ σl ∈ Icc (0 : ℝ) 1, StrictMonoOn (fun x => informativeness q γ ρ (x, σl))
      {x : ℝ | x ∈ Icc (0 : ℝ) 1 ∧ 1 - σl ≤ x}) ∧
    (∀ σh ∈ Icc (0 : ℝ) 1, StrictMonoOn (fun y => informativeness q γ ρ (σh, y))
      {y : ℝ | y ∈ Icc (0 : ℝ) 1 ∧ 1 - σh ≤ y}) := by sorry

end AnalystRank.Informativeness
