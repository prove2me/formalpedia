-- Prove2me | Theorems.Thm_CostlyShort_ShortMarket_eq14_lending_identity
-- name    : CostlyShort.ShortMarket.eq14_lending_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:35.351759+00:00
-- url     : https://prove2.me/theorems/94f5aa50-a504-4440-8825-869e3c618483
-- title:
--   (14), p. 18 — in equilibrium γσ₁S₁ = (φ − γ)(θ₁⁽ᵖ⁾ + φ)⁻W⁽ᵖ⁾
-- statement:
--   Fix one state $(\omega,t)$ of the economy (the time index is dropped) and an equilibrium in the sense of Definition 1 at that state (see the mission's definitions item): the volatilities $\sigma_1,\sigma_2>0$ of the two risky assets, the price $S_1>0$ of asset 1, the wealths $W^{(o)},W^{(p)}>0$ of the optimist $o$ and the pessimist $p$, their market prices of risk $\theta^{(a)}_1,\theta^{(a)}_2$ with $\theta^{(p)}_1\le\theta^{(o)}_1$ (disagreement $\Delta\ge0$), the lending yield $\gamma$ and shorting cost $\phi$ per unit of volatility, and the agents' optimal wealth fractions $p^{(o)},p^{(p)}$. The equilibrium conditions are (7), optimality in (8), clearing of asset 1 and of the lending market (5), and the shorting cost (4) chosen as the least revenue maximizer (13).
--
--   Then the lending yield and the shorting cost are related by
--   $$\gamma\,\sigma_1S_1=(\phi-\gamma)\,\big(\theta^{(p)}_1+\phi\big)^-\,W^{(p)},$$
--   where $m^-=\max\{-m,0\}$.
--
--   The identity comes from substituting the optimal portfolios of Proposition 1 into the two clearing conditions: the fees received by long holders equal the fees paid by short sellers, and only the pessimist shorts. It is the relation from which the paper reads off the inactive set $\mathcal L=\{\gamma=0\}$ in (15).
--
--   **Formalization Note** The equilibrium is the predicate `IsShortMarketEquilibrium` of the definitions item. Its shorting-cost condition is the per-volatility revenue (10) maximized over $y\ge\gamma$, with the least maximizer selected as in (13); (11), (13) and (14) are *not* assumed — they are derived results of the paper (separate items of this mission). Consumption clearing and asset-2 clearing are not part of the predicate, which makes the statement more general.
-- source:
--   Evgeniou, Hugonnier & Prieto, Asset Pricing with Costly Short Sales, SFI Research Paper N°22-21 (version of September 22, 2022), p. 18, (14)

import Mathlib
import Definitions.Def_CostlyShort_ShortMarket_Setting

namespace CostlyShort.ShortMarket

theorem eq14_lending_identity {σ₁ σ₂ S₁ Wo Wp θ₁o θ₁p θ₂o θ₂p γ φ : ℝ} {po pp : ℝ × ℝ}
    (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂) (hS₁ : 0 < S₁) (hWo : 0 < Wo) (hWp : 0 < Wp)
    (hΔ : θ₁p ≤ θ₁o)
    (heq : IsShortMarketEquilibrium σ₁ σ₂ S₁ Wo Wp θ₁o θ₁p θ₂o θ₂p γ φ po pp) :
    γ * σ₁ * S₁ = (φ - γ) * max (-(θ₁p + φ)) 0 * Wp := by sorry

end CostlyShort.ShortMarket
