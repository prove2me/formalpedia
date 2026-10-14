-- Prove2me | Theorems.Thm_CostlyShort_OneAsset_eq33_eq34_yield_from_cost
-- name    : CostlyShort.OneAsset.eq33_eq34_yield_from_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:25.664298+00:00
-- url     : https://prove2.me/theorems/6cda8c38-bd47-4f54-8f8d-cdfc99640bc6
-- title:
--   (33)–(34), §4.1, p. 28 — Γ = ΦΥ/(1 + Υ) with utilization Υ = ((1 − s)/σ²)Φ
-- statement:
--   Let $\sigma>0$, $s\in(0,1)$ and $\delta\ge 0$, and let $\Phi=\Phi(\sigma,\delta,s)$ and $\Gamma=\Gamma(\sigma,\delta,s)$ be the closed-form shorting cost (31) and lending yield (32). Define the utilization ratio by the outer equality of (34),
--   $$
--   \Upsilon=\frac{1-s}{\sigma^2}\,\Phi .
--   $$
--   Then the market-clearing relation (33) holds:
--   $$
--   \Gamma=\frac{\Phi\,\Upsilon}{1+\Upsilon}.
--   $$
--
--   This identity links the lending yield to the shorting cost through a function that is increasing and convex on $[0,\infty)$, which is how the paper transfers the comparative statics of $\Phi$ in $\delta$ to $\Gamma$.
--
--   **Formalization Note** The utilization ratio is defined in the paper as $\pi^{(p)-}_{1t}/S_{1t}$, the fraction of shortable shares on loan, and its middle expression in (34) comes from the agents' optimal portfolios in the continuous-time economy, which is not formalized. Only the identity between the closed forms that (33) and the outer equality of (34) yield is stated. Off the shorting region both sides are $0$.
-- source:
--   Evgeniou, Hugonnier & Prieto, Asset Pricing with Costly Short Sales, SFI Research Paper N°22-21 (version of September 22, 2022), §4.1, p. 28, (33) and (34)

import Mathlib
import Definitions.Def_CostlyShort_OneAsset_Setting

namespace CostlyShort.OneAsset

theorem eq33_eq34_yield_from_cost (σ δ s : ℝ) (hσ : 0 < σ) (hs0 : 0 < s) (hs1 : s < 1)
    (hδ : 0 ≤ δ) :
    yieldOne σ δ s = costOne σ δ s * ((1 - s) / σ ^ 2 * costOne σ δ s)
      / (1 + (1 - s) / σ ^ 2 * costOne σ δ s) := by sorry

end CostlyShort.OneAsset
