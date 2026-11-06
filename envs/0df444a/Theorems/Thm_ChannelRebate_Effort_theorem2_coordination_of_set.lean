-- Prove2me | Theorems.Thm_ChannelRebate_Effort_theorem2_coordination_of_set
-- name    : ChannelRebate.Effort.theorem2_coordination_of_set
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-06T00:04:35.518337+00:00
-- url     : https://prove2.me/theorems/6f6c4445-861d-4928-a8bd-2c1808953a3f
-- title:
--   Theorem 2, p. 1002 (parts (a)–(c) for a given contract) — any (w*, T*) set as in Theorem 2 has u*>0, b*∈(s,w*), coordinates, and splits profit κ / Π−κ
-- statement:
--   Let $0<c<p$, $s<c$, $a>0$, $\xi\sim\mathrm{Uniform}(0,1)$, $V(e)=ae^2/2$. Let $\bar Q_0$ solve $\Phi(\bar Q_0)=\frac{p-c}{p-s}$, $\bar e=(p-s)\Gamma(\bar Q_0)/a$, $\bar Q=\bar e\bar Q_0$ and $\Pi=\Lambda(\bar e)$, and fix $\kappa\in(0,\Pi)$. For a wholesale price $w$ and a target $T$ the contract $(w,u(T),b(T),T)$ uses the rebate $u(T)$ and return credit $b(T)$ of p. 1001; $T_1(w)$, $T_2(w)$ are the fixed points of $m_1(T)=\underline e\tau$ and $m_2(T)=\bar e\tau$ (Lemma 6), $\underline L(T,w)$ is the retailer's profit at effort $\underline e$ and order $\underline e\,\underline Q_0$, and $\bar L(T)$ her profit at effort $\bar e$ and order $\bar e\,\underline Q_1$. Say $(w^*,T^*)$ is *set as in Theorem 2* for $\varepsilon$ when $w^*\in(c,p)$, $T^*\in(T_1(w^*),T_2(w^*))$ (for some fixed points $T_1,T_2$), $\underline L(T^*,w^*)=\kappa-\varepsilon$ and $\bar L(T^*)=\kappa$.
--
--   **Claim.** Let $\varepsilon\in(0,\kappa)$ and let $(w^*,T^*)$ be set as in Theorem 2 for $\varepsilon$; write $u^*=u(T^*)$, $b^*=b(T^*)$. Then
--
--   1. $u^*>0$, $s<b^*<w^*$ and $T^*>0$;
--   2. $(\bar Q,\bar e)$ is the unique maximizer of the retailer's profit $R(Q,e\mid T^*)$ over $Q\ge 0$, $e\ge 0$ (channel coordination);
--   3. $R(\bar Q,\bar e\mid T^*)=\kappa$ and the manufacturer's profit is $M(\bar Q,\bar e\mid T^*)=\Pi-\kappa$.
--
--   This is the "for every such pair" half of Theorem 2 (the conclusions of (a), and (b), (c)); it holds for every $\varepsilon\in(0,\kappa)$, no smallness being needed. The manufacturer's profit $M$ is defined from the cash flows (wholesale revenue, rebate paid, units bought back at $b$ and salvaged at $s$), so that $R+M$ is the integrated-channel profit.
-- source:
--   Taylor, Supply Chain Coordination Under Channel Rebates with Sales Effort Effects, Management Science 48(8) (2002), p. 1002, Theorem 2 (with u(T), b(T), T₁, T₂ of p. 1001 and L̲, L̄ of p. 1002); proof pp. 1005–1006

import Mathlib
import Definitions.Def_ChannelRebate_Effort_Setting

open MeasureTheory Filter Topology

namespace ChannelRebate.Effort

theorem theorem2_coordination_of_set
    (p c s a : ℝ) (hc : 0 < c) (hcp : c < p) (hsc : s < c) (ha : 0 < a)
    (Qb : ℝ) (hQb : IsQbar0 p c s Qb)
    (κ : ℝ) (hκ0 : 0 < κ) (hκPi : κ < Lam a (ebarOf p s a Qb))
    (ε : ℝ) (hε : 0 < ε) (hεκ : ε < κ) :
    ∀ w T : ℝ, c < w → w < p →
      (∃ T₁ T₂ : ℝ, IsFixed1 p c s a w T₁ ∧ IsFixed2 p c s a w T₂ ∧ T₁ < T ∧ T < T₂) →
      IsLlow p c s a w T (κ - ε) → IsLbar p c s a w T κ →
        (0 < uT p c s a w T ∧ s < bT p c s a w T ∧ bT p c s a w T < w ∧ 0 < T) ∧
        optimalPairs (R p w (uT p c s a w T) (bT p c s a w T) a T) =
          {(ebarOf p s a Qb * Qb, ebarOf p s a Qb)} ∧
        R p w (uT p c s a w T) (bT p c s a w T) a T
            (ebarOf p s a Qb * Qb) (ebarOf p s a Qb) = κ ∧
        M c s w (uT p c s a w T) (bT p c s a w T) T
            (ebarOf p s a Qb * Qb) (ebarOf p s a Qb) = Lam a (ebarOf p s a Qb) - κ := by sorry

end ChannelRebate.Effort
