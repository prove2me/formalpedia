-- Prove2me | Theorems.Thm_ChannelRebate_Quantity_theorem1_target_rebate_coordination
-- name    : ChannelRebate.Quantity.theorem1_target_rebate_coordination
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:13:00.131307+00:00
-- url     : https://prove2.me/theorems/910fc47f-83d1-46db-8e2c-350517d97410
-- title:
--   Theorem 1, p. 996 — for κ ∈ (0, π) and small ε the target rebate (w*, û(w*), T*) exists uniquely, coordinates the channel and gives r* = κ, m* = π − κ
-- statement:
--   Let demand $\xi$ have a density $\varphi$ that vanishes on $(-\infty,0)$ and is positive on $[0,\infty)$ (Assumption A4), with finite mean, distribution $\Phi$ and $\Gamma(Q) = \int_0^Q \xi\,d\Phi(\xi)$. Let $0 < c < p$ and $s < c$, let $\bar Q_0 > 0$ satisfy $\Phi(\bar Q_0) = (p-c)/(p-s)$, and let $\pi = (p-s)\Gamma(\bar Q_0)$ be the integrated-channel profit. Write $\hat u(w) = (w-c)(p-s)/(c-s)$ and, for a wholesale price $w$, let $\underline r(w) = -wQ_0 + pE\min(Q_0,\xi) + sE(Q_0-\xi)^+$ be the retailer's profit under the wholesale price-only contract at the order $Q_0 \ge 0$ with $\Phi(Q_0) = (p-w)/(p-s)$.
--
--   Fix $\kappa \in (0,\pi)$. Then there is $\varepsilon_0 > 0$ such that for every $\varepsilon \in (0,\kappa)$ with $\varepsilon < \varepsilon_0$ there is **exactly one** triple $(w^*,u^*,T^*)$ of reals satisfying the contract specification
--   1. $\underline r(w^*) = \kappa - \varepsilon$;
--   2. $u^* = \hat u(w^*)$;
--   3. $T^* \ge 0$ and
--   $$
--   (p+u^*-s)\Gamma(\bar Q_0) - u^*\big(\Gamma(T^*) + T^*[1-\Phi(T^*)]\big) = \kappa, \qquad (1)
--   $$
--
--   and this triple satisfies
--   - **(a)** $w^* \in (c,p)$, $u^* > 0$, $T^* > 0$;
--   - **(b)** channel coordination: $\bar Q_0$ is the retailer's unique optimal order under $(w^*,u^*,T^*)$, $\arg\max_{Q\ge 0} r(Q\mid T^*) = \{\bar Q_0\}$;
--   - **(c)** the retailer earns $r^* = r(\bar Q_0\mid T^*) = \kappa$ and the manufacturer earns $m^* = (w^*-c)\bar Q_0 - u^*E(\min(\bar Q_0,\xi)-T^*)^+ = \pi - \kappa$.
--
--   The theorem shows that a target rebate, with no side payment, coordinates the newsvendor channel and splits its profit in any proportion.
--
--   **Formalization Note** "For $\varepsilon$ sufficiently small" is the existence of the threshold $\varepsilon_0$. Uniqueness ranges over all real triples satisfying 1–3, with $w$ unrestricted; that $w^* \in (c,p)$ is part of the conclusion. Coordination is stated as equality of the set of maximizers over $Q \ge 0$ with $\{\bar Q_0\}$, i.e. global optimality, not a first-order condition.
-- source:
--   Taylor, Supply Chain Coordination Under Channel Rebates with Sales Effort Effects, Management Science 48(8) (2002), p. 996, Theorem 1 and display (1); proof p. 1005

import Mathlib
import Definitions.Def_CachonCoord_Newsvendor_Contracts
import Definitions.Def_ChannelRebate_Quantity_Setting
open MeasureTheory

namespace ChannelRebate.Quantity

/-- Taylor (2002), Theorem 1 and display (1), p. 996. For `κ ∈ (0, π)`, `π = (p − s)Γ(Q̄₀)`,
and every sufficiently small `ε ∈ (0, κ)`, there is exactly one triple `(w*, u*, T*)` with
(1) `r̲(w*) = κ − ε`, (2) `u* = û(w*)`, (3) `T* ≥ 0` solving (1); and it satisfies
(a) `w* ∈ (c, p)`, `u* > 0`, `T* > 0`; (b) the retailer's unique optimal order is `Q̄₀`
(channel coordination); (c) `r* = κ` and `m* = π − κ`. -/
theorem theorem1_target_rebate_coordination (p c s : ℝ) (hc : 0 < c) (hcp : c < p)
    (hsc : s < c) (D : Demand)
    (Qbar0 : ℝ) (hQbar0 : 0 < Qbar0) (hΦbar : Phi D Qbar0 = (p - c) / (p - s))
    (κ : ℝ) (hκ0 : 0 < κ) (hκπ : κ < (p - s) * Gam D Qbar0) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → ε < κ →
      ∃! x : ℝ × ℝ × ℝ,
        -- the contract specification (1)–(3), with x = (w, u, T)
        ((∃ Q0 : ℝ, 0 ≤ Q0 ∧ Phi D Q0 = (p - x.1) / (p - s) ∧
            wholesaleProfit p s x.1 D Q0 = κ - ε) ∧
          x.2.1 = uHat p c s x.1 ∧
          0 ≤ x.2.2 ∧
          (p + x.2.1 - s) * Gam D Qbar0
            - x.2.1 * (Gam D x.2.2 + x.2.2 * (1 - Phi D x.2.2)) = κ) ∧
        -- (a)
        (c < x.1 ∧ x.1 < p ∧ 0 < x.2.1 ∧ 0 < x.2.2) ∧
        -- (b) channel coordination
        optimalOrders (retailerProfit p s x.1 x.2.1 x.2.2 D) = {Qbar0} ∧
        -- (c)
        retailerProfit p s x.1 x.2.1 x.2.2 D Qbar0 = κ ∧
        manufProfit c x.1 x.2.1 x.2.2 D Qbar0 = (p - s) * Gam D Qbar0 - κ := by sorry

end ChannelRebate.Quantity
