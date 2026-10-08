-- Prove2me | Theorems.Thm_CachonCoord_CapacityForecast_p101_inducing_price
-- name    : CachonCoord.CapacityForecast.p101_inducing_price
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:10:46.886982+00:00
-- url     : https://prove2.me/theorems/ca0444bc-17f4-4d54-838b-17e093ba3da2
-- title:
--   §6.10.2, p. 101 — k > 0 is optimal for the supplier iff w = w_θ(k) = c_k/F̄_θ(k) + c_p
-- statement:
--   Under a wholesale price contract with price $w$, the supplier's expected profit from building capacity $k$ is
--   $$\pi_\theta(k) = (w - c_p)S_\theta(k) - c_k k .$$
--   For every positive capacity $k$, $k$ maximizes $\pi_\theta$ over $[0,\infty)$ if and only if $\bar F_\theta(k) > 0$ and
--   $$w = w_\theta(k) = \frac{c_k}{\bar F_\theta(k)} + c_p .$$
--   In particular there is exactly one wholesale price inducing $k$ whenever $\bar F_\theta(k) > 0$, which lets the manufacturer choose capacity through the price and write her profit as $\Pi_\theta(k) = (r - w_\theta(k))S_\theta(k)$.
--
--   **Formalization Note** The page derives uniqueness from strict concavity of $\pi_\theta$ in $k$; strict concavity needs $F_\theta$ strictly increasing, which the model of p. 97 does not assume, so it is not stated. The uniqueness of the inducing price holds without it and is what the statement asserts. Capacities are positive (footnote 46 ignores boundary solutions).
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.10.2, p. 101, the displays π_θ(k) and w_θ(k)

import Mathlib
import Definitions.Def_CachonCoord_CapacityForecast_Model
import Definitions.Def_CachonCoord_CapacityForecast_Contracts

open MeasureTheory ProbabilityTheory

namespace CachonCoord.CapacityForecast

/-- Cachon (2003), 3rd draft, §6.10.2, p. 101: with a wholesale price contract the supplier's
profit is `π_θ(k) = (w − c_p) S_θ(k) − c_k k`, and for every positive capacity `k` there is exactly
one wholesale price making `k` optimal for the supplier (a maximizer of `π_θ` over `k ≥ 0`), namely
`w_θ(k) = c_k / F̄_θ(k) + c_p`; such a price exists exactly when `F̄_θ(k) > 0`. -/
theorem p101_inducing_price (M : Model) (θ : DemandType) (k w : ℝ) (hk : 0 < k) :
    IsMaxOn (M.supWholesaleProfit θ w) (Set.Ici 0) k ↔
      (0 < 1 - cdf (M.μ θ) k ∧ w = M.wInduce θ k) := by sorry

end CachonCoord.CapacityForecast
