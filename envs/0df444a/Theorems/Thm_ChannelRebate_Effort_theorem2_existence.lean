-- Prove2me | Theorems.Thm_ChannelRebate_Effort_theorem2_existence
-- name    : ChannelRebate.Effort.theorem2_existence
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-06T00:04:30.31305+00:00
-- url     : https://prove2.me/theorems/b730e021-2adc-492e-a901-37310f5d12a2
-- title:
--   Theorem 2, p. 1002 (existence part) — for small ε a target rebate and returns contract (w*, T*) set as in Theorem 2 exists
-- statement:
--   Let $0<c<p$, $s<c$, $a>0$, $\xi\sim\mathrm{Uniform}(0,1)$, $V(e)=ae^2/2$. Let $\bar Q_0$ solve $\Phi(\bar Q_0)=\frac{p-c}{p-s}$, $\bar e=(p-s)\Gamma(\bar Q_0)/a$, $\bar Q=\bar e\bar Q_0$ and $\Pi=\Lambda(\bar e)$, and fix $\kappa\in(0,\Pi)$. For a wholesale price $w$ and a target $T$ the contract $(w,u(T),b(T),T)$ uses the rebate $u(T)$ and return credit $b(T)$ of p. 1001; $T_1(w)$, $T_2(w)$ are the fixed points of $m_1(T)=\underline e\tau$ and $m_2(T)=\bar e\tau$ (Lemma 6), $\underline L(T,w)$ is the retailer's profit at effort $\underline e$ and order $\underline e\,\underline Q_0$, and $\bar L(T)$ her profit at effort $\bar e$ and order $\bar e\,\underline Q_1$. Say $(w^*,T^*)$ is *set as in Theorem 2* for $\varepsilon$ when $w^*\in(c,p)$, $T^*\in(T_1(w^*),T_2(w^*))$ (for some fixed points $T_1,T_2$), $\underline L(T^*,w^*)=\kappa-\varepsilon$ and $\bar L(T^*)=\kappa$.
--
--   **Claim (existence half of Theorem 2(a)).** There is $\varepsilon_0>0$ (depending only on $p,c,s,a,\kappa$) such that for every $\varepsilon\in(0,\kappa)$ with $\varepsilon<\varepsilon_0$ there exist $w^*\in(c,p)$ and $T^*$, together with fixed points $T_1<T^*<T_2$ of $m_1,m_2$ at $w^*$, with $\underline L(T^*,w^*)=\kappa-\varepsilon$ and $\bar L(T^*)=\kappa$.
--
--   In the paper this is the intermediate-value argument of the proof of Theorem 2 (p. 1005–1006): for each $T$ the equation $\underline L(T,w)=\kappa-\varepsilon$ determines $w^*(T)\in(c,p)$, and $T^*$ is a root of $\bar L-\underline L-\varepsilon$ on $(T_1,T_2)$. The fixed points $T_1,T_2$ are given by their defining equations (Lemma 6).
-- source:
--   Taylor, Supply Chain Coordination Under Channel Rebates with Sales Effort Effects, Management Science 48(8) (2002), p. 1002, Theorem 2 (with u(T), b(T), T₁, T₂ of p. 1001 and L̲, L̄ of p. 1002); proof pp. 1005–1006

import Mathlib
import Definitions.Def_ChannelRebate_Effort_Setting

open MeasureTheory Filter Topology

namespace ChannelRebate.Effort

theorem theorem2_existence
    (p c s a : ℝ) (hc : 0 < c) (hcp : c < p) (hsc : s < c) (ha : 0 < a)
    (Qb : ℝ) (hQb : IsQbar0 p c s Qb)
    (κ : ℝ) (hκ0 : 0 < κ) (hκPi : κ < Lam a (ebarOf p s a Qb)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ε < κ →
      ∃ w T : ℝ, c < w ∧ w < p ∧
        (∃ T₁ T₂ : ℝ, IsFixed1 p c s a w T₁ ∧ IsFixed2 p c s a w T₂ ∧ T₁ < T ∧ T < T₂) ∧
        IsLlow p c s a w T (κ - ε) ∧ IsLbar p c s a w T κ := by sorry

end ChannelRebate.Effort
