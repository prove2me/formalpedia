-- Prove2me | Theorems.Thm_ChannelRebate_Effort_lemma5_optimal_effort_quantity
-- name    : ChannelRebate.Effort.lemma5_optimal_effort_quantity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:13:18.073153+00:00
-- url     : https://prove2.me/theorems/94717f05-33b0-4b6d-92d5-efd73351f69b
-- title:
--   Lemma 5, p. 1001 — the retailer's optimal (Q, e) is (êQ̲₁, ê) if T < ϒ, (e̲Q̲₀, e̲) if T > ϒ, and both if T = ϒ
-- statement:
--   In the setting of Lemma 4 ($0<c<w<p$, $s<c$, $a>0$, $u>0$, $b\in[s,w)$, $T>0$, $\xi\sim\mathrm{Uniform}(0,1)$, $V(e)=ae^2/2$), let $\Upsilon\ge\tau\underline e$ satisfy $j(\Upsilon)=0$. Let $(Q^*,e^*)$ range over the maximizers of $R(Q,e\mid T)$ over $Q\ge0$, $e\ge0$, and put $Q_2=\underline e\,\underline Q_0$ and $Q_3=\hat e\,\underline Q_1$.
--
--   1. If $T<\Upsilon$, the unique maximizer is $(Q_3,\hat e)$, for a single effort level $\hat e>T/\tau$.
--   2. If $T>\Upsilon$, the unique maximizer is $(Q_2,\underline e)$.
--   3. If $T=\Upsilon$, the maximizers are exactly $(Q_2,\underline e)$ and $(Q_3,\hat e)$, with $\hat e>T/\tau$.
--
--   This is the retailer's complete best response to a target rebate and returns contract, on which the coordination claim of Theorem 2 rests.
--
--   **Formalization Note.** The paper writes the pairs as $(e^*,Q^*)$; they are written here in the order $(Q,e)$ used for $R(Q,e\mid T)$. $\Upsilon$ is taken as a hypothesis through its defining equation $j(\Upsilon)=0$ on $[\tau\underline e,\infty)$; Lemma 4(a) makes it unique. As in Lemma 4, $\hat e$ is identified as the effort level above $T/\tau$ at which the maximum is attained.
-- source:
--   Taylor, Supply Chain Coordination Under Channel Rebates with Sales Effort Effects, Management Science 48(8) (2002), p. 1001, Lemma 5

import Mathlib
import Definitions.Def_ChannelRebate_Effort_Setting

open MeasureTheory Filter Topology

namespace ChannelRebate.Effort

theorem lemma5_optimal_effort_quantity
    (p c s w a u b T : ℝ) (hc : 0 < c) (hcw : c < w) (hwp : w < p) (hsc : s < c) (ha : 0 < a)
    (hu : 0 < u) (hsb : s ≤ b) (hbw : b < w) (hT : 0 < T)
    (Q0 Q1 τ : ℝ) (hQ0 : IsQlow0 p w b Q0) (hQ1 : IsQlow1 p w u b Q1) (hτ : IsTau p w u b τ)
    (Υ : ℝ) (hΥ : τ * elowOf p b a Q0 ≤ Υ) (hj : IsJ p w u b a τ Υ 0) :
    (T < Υ → ∃ eh, T / τ < eh ∧ optimalPairs (R p w u b a T) = {(eh * Q1, eh)}) ∧
      (Υ < T → optimalPairs (R p w u b a T) = {(elowOf p b a Q0 * Q0, elowOf p b a Q0)}) ∧
      (T = Υ → ∃ eh, T / τ < eh ∧
        optimalPairs (R p w u b a T) = {(elowOf p b a Q0 * Q0, elowOf p b a Q0), (eh * Q1, eh)}) := by sorry

end ChannelRebate.Effort
