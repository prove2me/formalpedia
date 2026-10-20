-- Prove2me | Theorems.Thm_ChainCompSI_Backfire_proposition_2
-- name    : ChainCompSI.Backfire.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:22:59.371601+00:00
-- url     : https://prove2.me/theorems/49bce4e8-e080-45d7-a8e9-41308dcd467e
-- title:
--   Proposition 2, p. 12 — under fierce chain-to-chain competition strategic inventories leave all firms strictly worse off
-- statement:
--   Let $h \ge 0$ be the unit holding cost.
--
--   1. Suppose $h < 1/4$. Then there exists $\theta_0 \ge 0$ with $\theta_0 < 1/h - 4$ such that for every $\theta$ with
--   $$\theta_0 < \theta < \frac1h - 4,$$
--   both the strategic-inventory game (SI) and the no-inventory game (NI) have passive-beliefs equilibria, and for any SI equilibrium $E$ and any NI equilibrium $E'$, every firm is strictly worse off under SI:
--   $$\Pi_i(E) < \Pi_i(E') \quad\text{and}\quad \pi_i(E) < \pi_i(E') \qquad (i = 1, 2).$$
--   2. If $\theta > 0$ and $h \ge 1/4$ or $\theta \ge 1/h - 4$, then the SI game has an equilibrium, and in every SI equilibrium no strategic inventory is carried: $I_i = 0$ for both chains.
--
--   In a monopoly supply chain strategic inventory benefits both firms by alleviating double marginalization. This result shows that under sufficiently fierce chain-to-chain competition the same mechanism intensifies competition between the chains enough to hurt both manufacturers and both retailers.
--
--   **Formalization Note** The condition $\theta < 1/h - 4$ is written as $h(4+\theta) < 1$, and $\theta \ge 1/h - 4$ as $h(4+\theta) \ge 1$. These agree for $h > 0$; for $h = 0$ the page's bound $1/h - 4$ is $+\infty$, and the product form keeps that case (every $\theta > \theta_0$ qualifies), whereas Lean's $1/0 = 0$ would not. The existence of equilibria is part of each claim, so that neither is vacuous. "All firms" means both manufacturers and both retailers; profits are realized equilibrium profits, the retailer's including the holding cost.
-- source:
--   Li, Li & Chen, Strategic Inventories under Supply Chain Competition, SSRN 3003887 (author's copy), p. 12, Proposition 2 (with its parenthetical)

import Mathlib
import Definitions.Def_ChainCompSI_Backfire_Model

namespace ChainCompSI.Backfire

theorem proposition_2 (h : ℝ) (hh : 0 ≤ h) : (h < 1 / 4 → ∃ θ0 : ℝ, 0 ≤ θ0 ∧ h * (4 + θ0) < 1 ∧ ∀ θ : ℝ, θ0 < θ → h * (4 + θ) < 1 → (∃ E, IsEq θ h SI E) ∧ (∃ E', IsEq θ h NI E') ∧ ∀ E E', IsEq θ h SI E → IsEq θ h NI E' → ∀ i : Fin 2, mfrProfit θ E i < mfrProfit θ E' i ∧ retProfit θ h E i < retProfit θ h E' i) ∧ (∀ θ : ℝ, 0 < θ → (1 / 4 ≤ h ∨ 1 ≤ h * (4 + θ)) → (∃ E, IsEq θ h SI E) ∧ ∀ E, IsEq θ h SI E → ∀ i : Fin 2, E.inv i = 0) := by sorry

end ChainCompSI.Backfire
