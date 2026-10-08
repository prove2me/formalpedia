-- Prove2me | Theorems.Thm_CachonCoord_CapacityForecast_p102_not_coordinated
-- name    : CachonCoord.CapacityForecast.p102_not_coordinated
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:10:52.115275+00:00
-- url     : https://prove2.me/theorems/e1cc29bb-c56e-4b84-86fe-6c3cad69c234
-- title:
--   §6.10.2, p. 102 — Π′_θ(k*) = 0 gives F̄_θ(k*) = F̄_θ(k_θ°)(1 + f_θ(k*)S_θ(k*)/F̄_θ(k*)²), so k* < k_θ°
-- statement:
--   Under voluntary compliance the manufacturer offers a wholesale price contract and, by choosing $w = w_\theta(k)$, induces capacity $k$, earning $\Pi_\theta(k) = (r - w_\theta(k))S_\theta(k)$. Let $k^* > 0$ be a stationary point, $\Pi'_\theta(k^*) = 0$, at which $\bar F_\theta(k^*) > 0$ and $F_\theta$ has derivative $f_\theta(k^*) > 0$. Let $k_\theta^o > 0$ be an optimal capacity of the integrated chain. Then
--   $$\bar F_\theta(k^*) = \frac{c_k}{r - c_p}\left(1 + \frac{f_\theta(k^*)}{\bar F_\theta(k^*)^2}S_\theta(k^*)\right) = \bar F_\theta(k_\theta^o)\left(1 + \frac{f_\theta(k^*)}{\bar F_\theta(k^*)^2}S_\theta(k^*)\right),$$
--   and the supply chain is not coordinated: $k^* < k_\theta^o$.
--
--   The wholesale price contract thus builds too little capacity, which is the cost of voluntary compliance.
--
--   **Formalization Note** The page assumes $w''_\theta > 0$ to make $\Pi_\theta$ strictly concave, so that the stationary point is the unique optimum $k_\theta^*$; the identity and $k^* < k_\theta^o$ follow from stationarity alone and are stated for any stationary point, without that assumption. $\bar F_\theta(k^*) > 0$ is assumed because the page divides by it (with $\bar F_\theta(k^*) = 0$ Lean's $x/0 = 0$ would make $w_\theta(k^*) = c_p$). $f_\theta(k^*) > 0$ is assumed because with $f_\theta(k^*) = 0$ the inequality $k^* < k_\theta^o$ can fail ($k^*$ is then itself an optimal capacity of the chain).
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.10.2, p. 102, the display following 'It follows from Π′_θ(k_θ*) = 0 that the supply chain is not coordinated, k_θ* < k_θ°'

import Mathlib
import Definitions.Def_CachonCoord_CapacityForecast_Model
import Definitions.Def_CachonCoord_CapacityForecast_Contracts

open MeasureTheory ProbabilityTheory

namespace CachonCoord.CapacityForecast

/-- Cachon (2003), 3rd draft, §6.10.2, p. 102: if `k* > 0` is a stationary point of the
manufacturer's wholesale-price profit `Π_θ(k) = (r − w_θ(k)) S_θ(k)` (`Π'_θ(k*) = 0`), where
`F̄_θ(k*) > 0` and `F_θ` has derivative `f_θ(k*) > 0` at `k*`, then
`F̄_θ(k*) = (c_k/(r − c_p)) (1 + f_θ(k*) S_θ(k*) / F̄_θ(k*)²) = F̄_θ(k_θ°) (1 + f_θ(k*) S_θ(k*) / F̄_θ(k*)²)`
for an optimal capacity `k_θ° > 0`, and the supply chain is not coordinated: `k* < k_θ°`. -/
theorem p102_not_coordinated (M : Model) (θ : DemandType) (kstar fk : ℝ) (hks : 0 < kstar)
    (hFbar : 0 < 1 - cdf (M.μ θ) kstar)
    (hf : HasDerivAt (cdf (M.μ θ)) fk kstar) (hfk : 0 < fk)
    (hstat : HasDerivAt (M.mfrWholesaleProfit θ) 0 kstar)
    (ko : ℝ) (hko : IsMaxOn (M.Omega θ) (Set.Ici 0) ko) (hko_pos : 0 < ko) :
    1 - cdf (M.μ θ) kstar
        = M.ck / (M.r - M.cp) * (1 + fk / (1 - cdf (M.μ θ) kstar) ^ 2 * M.S θ kstar) ∧
      1 - cdf (M.μ θ) kstar
        = (1 - cdf (M.μ θ) ko) * (1 + fk / (1 - cdf (M.μ θ) kstar) ^ 2 * M.S θ kstar) ∧
      kstar < ko := by sorry

end CachonCoord.CapacityForecast
