-- Prove2me | Theorems.Thm_CostlyShort_ShortMarket_eq15_eq16_shorting_cost
-- name    : CostlyShort.ShortMarket.eq15_eq16_shorting_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:34.837792+00:00
-- url     : https://prove2.me/theorems/9888a6e1-ef42-4363-b04e-b013254e8a80
-- title:
--   (15)–(17), p. 19 — lending is inactive exactly when θ₂⁽ᵖ⁾ ≥ 0, and the shorting cost is φ = −½θ₁⁽ᵖ⁾ 1_S
-- statement:
--   Fix one state $(\omega,t)$ of the economy (the time index is dropped) and an equilibrium in the sense of Definition 1 at that state (see the mission's definitions item): the volatilities $\sigma_1,\sigma_2>0$ of the two risky assets, the price $S_1>0$ of asset 1, the wealths $W^{(o)},W^{(p)}>0$ of the optimist $o$ and the pessimist $p$, their market prices of risk $\theta^{(a)}_1,\theta^{(a)}_2$ with $\theta^{(p)}_1\le\theta^{(o)}_1$ (disagreement $\Delta\ge0$), the lending yield $\gamma$ and shorting cost $\phi$ per unit of volatility, and the agents' optimal wealth fractions $p^{(o)},p^{(p)}$. The equilibrium conditions are (7), optimality in (8), clearing of asset 1 and of the lending market (5), and the shorting cost (4) chosen as the least revenue maximizer (13).
--
--   Then:
--
--   1. the shorting market is inactive exactly when the pessimist's net Sharpe ratio is nonnegative,
--   $$\gamma=0\iff\theta^{(p)}_2\ge0 ,$$
--   which is (15), $\mathcal L=\{\gamma=0\}=\{\theta^{(p)}_2\ge0\}$, and its complement (17), $\mathcal S=\{\theta^{(p)}_2<0\}$;
--   2. the shorting cost per unit of volatility is half the pessimist's frictionless Sharpe ratio on the active set, and zero elsewhere,
--   $$\phi=-\tfrac12\,\theta^{(p)}_1\,\mathbb 1_{\mathcal S}. \tag{16}$$
--
--   This is the paper's characterization of the equilibrium short market: the lending agent, acting as a monopolist on behalf of asset owners, charges one half of the Sharpe ratio $-\theta^{(p)}_1$ the pessimist could earn by shorting absent frictions, and lending is active exactly where the pessimist perceives a strictly negative net Sharpe ratio $\theta^{(p)}_2=\theta^{(p)}_1+\gamma$ on long positions.
--
--   **Formalization Note** The equilibrium is the predicate `IsShortMarketEquilibrium` of the definitions item. Its shorting-cost condition is the per-volatility revenue (10) maximized over $y\ge\gamma$, with the least maximizer selected as in (13); (11), (13) and (14) are *not* assumed — they are derived results of the paper (separate items of this mission). Consumption clearing and asset-2 clearing are not part of the predicate, which makes the statement more general. In particular the equilibrium does not assume $\phi>\gamma$: on the inactive set $\gamma=\phi=0$ is reached, and the statement covers it.
-- source:
--   Evgeniou, Hugonnier & Prieto, Asset Pricing with Costly Short Sales, SFI Research Paper N°22-21 (version of September 22, 2022), p. 19, (15)–(17); proof of (15) in App. A, p. 50

import Mathlib
import Definitions.Def_CostlyShort_ShortMarket_Setting

namespace CostlyShort.ShortMarket

theorem eq15_eq16_shorting_cost {σ₁ σ₂ S₁ Wo Wp θ₁o θ₁p θ₂o θ₂p γ φ : ℝ} {po pp : ℝ × ℝ}
    (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂) (hS₁ : 0 < S₁) (hWo : 0 < Wo) (hWp : 0 < Wp)
    (hΔ : θ₁p ≤ θ₁o)
    (heq : IsShortMarketEquilibrium σ₁ σ₂ S₁ Wo Wp θ₁o θ₁p θ₂o θ₂p γ φ po pp) :
    (γ = 0 ↔ 0 ≤ θ₂p) ∧ φ = (if θ₂p < 0 then -θ₁p / 2 else 0) := by sorry

end CostlyShort.ShortMarket
