-- Prove2me | Theorems.Thm_ChannelRebate_Effort_theorem2_rebate_returns_coordination
-- name    : ChannelRebate.Effort.theorem2_rebate_returns_coordination
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:13:21.638362+00:00
-- url     : https://prove2.me/theorems/c480fe98-c6f5-4b29-9444-d0ef5d83ed32
-- title:
--   Theorem 2, p. 1002 — under ξ ∼ U(0,1), for κ ∈ (0, Π) and small ε the target rebate and returns contract (w*, u(T*), b(T*), T*) exists, coordinates effort and quantity, and gives R* = κ, M* = Π − κ
-- statement:
--   Let $0<c<p$, $s<c$, $a>0$, let $\xi\sim\mathrm{Uniform}(0,1)$ and $V(e)=ae^2/2$. Let $\bar Q_0$ solve $\Phi(\bar Q_0)=\frac{p-c}{p-s}$, $\bar e=(p-s)\Gamma(\bar Q_0)/a$, $\bar Q=\bar e\bar Q_0$, and let $\Pi=\Lambda(\bar e)$ be the integrated channel's optimal profit. Fix $\kappa\in(0,\Pi)$.
--
--   For a wholesale price $w\in(c,p)$ and a target $T$, the contract $(w,u(T),b(T),T)$ uses the rebate $u(T)$ and return credit $b(T)$ of p. 1001; $T_1(w)$ and $T_2(w)$ are the fixed points of Lemma 6, $\underline L(T,w)$ the retailer's profit at effort $\underline e$ and $\bar L(T)$ her profit at effort $\bar e$. Say that $(w^*,T^*)$ is **set as in Theorem 2** for $\varepsilon$ when
--   $$T^*\in(T_1,T_2),\qquad \underline L(T^*,w^*)=\kappa-\varepsilon,\qquad \bar L(T^*)=\kappa .$$
--
--   Then there is $\varepsilon_0>0$ such that for every $\varepsilon\in(0,\kappa)$ with $\varepsilon<\varepsilon_0$:
--
--   1. **(a)** such $(w^*,T^*)$ exist; and for every such pair, with $u^*=u(T^*)$ and $b^*=b(T^*)$, we have $w^*\in(c,p)$, $u^*>0$, $b^*\in(s,w^*)$ and $T^*>0$;
--   2. **(b)** the contract achieves channel coordination: $(\bar Q,\bar e)$ is the unique maximizer of the retailer's profit $R(Q,e\mid T^*)$ over $Q\ge0$, $e\ge0$;
--   3. **(c)** the resulting profits are $R^*=R(\bar Q,\bar e\mid T^*)=\kappa$ for the retailer and $M^*=M(\bar Q,\bar e\mid T^*)=\Pi-\kappa$ for the manufacturer.
--
--   So a target rebate combined with returns, unlike either instrument alone, aligns both the retailer's effort and her order with the integrated channel's and can split the channel profit in any proportion.
--
--   **Formalization Note.** $\varepsilon_0$ depends on $p,c,s,a,\kappa$ only. Part (a) is stated as existence plus, for every pair set this way, the listed inequalities; (b) and (c) are claimed for every such pair. $w\in(c,p)$ is the standing Assumption A1 and is part of "set as in Theorem 2". $T_1$, $T_2$, $\underline L$, $\bar L$ are given by their defining equations; $\bar L$ depends on $w$ through $u(T)$ and $b(T)$, though the paper writes $\bar L(T)$. The manufacturer's profit $M$ is not displayed in the paper; it is defined from the cash flows (wholesale revenue, rebate paid, units bought back at $b$ and salvaged at $s$), so that $R+M=\Pi$.
-- source:
--   Taylor, Supply Chain Coordination Under Channel Rebates with Sales Effort Effects, Management Science 48(8) (2002), p. 1002, Theorem 2 (with u(T), b(T), T₁, T₂ of p. 1001 and L̲, L̄ of p. 1002); proof pp. 1005–1006

import Mathlib
import Definitions.Def_ChannelRebate_Effort_Setting

open MeasureTheory Filter Topology

namespace ChannelRebate.Effort

theorem theorem2_rebate_returns_coordination
    (p c s a : ℝ) (hc : 0 < c) (hcp : c < p) (hsc : s < c) (ha : 0 < a)
    (Qb : ℝ) (hQb : IsQbar0 p c s Qb)
    (κ : ℝ) (hκ0 : 0 < κ) (hκPi : κ < Lam a (ebarOf p s a Qb)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ε < κ →
      (∃ w T : ℝ, c < w ∧ w < p ∧
          (∃ T₁ T₂ : ℝ, IsFixed1 p c s a w T₁ ∧ IsFixed2 p c s a w T₂ ∧ T₁ < T ∧ T < T₂) ∧
          IsLlow p c s a w T (κ - ε) ∧ IsLbar p c s a w T κ) ∧
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
