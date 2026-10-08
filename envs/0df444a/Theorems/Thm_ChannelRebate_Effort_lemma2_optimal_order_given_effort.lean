-- Prove2me | Theorems.Thm_ChannelRebate_Effort_lemma2_optimal_order_given_effort
-- name    : ChannelRebate.Effort.lemma2_optimal_order_given_effort
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:13:59.069508+00:00
-- url     : https://prove2.me/theorems/e2d6e311-2788-48b4-91bf-0ace570e978a
-- title:
--   Lemma 2, p. 1000 — for given effort e, the retailer orders Q₂ = eQ̲₀ if e < T/τ, Q₃ = eQ̲₁ if e > T/τ, either if e = T/τ
-- statement:
--   Let $0<c<w<p$, $s<c$, $a>0$, and consider a target rebate and returns contract $(w,u,b,T)$ with $u>0$, $b\in[s,w)$ and $T>0$. Let $\xi\sim\mathrm{Uniform}(0,1)$ and $V(e)=ae^2/2$. Let $\underline Q_0,\underline Q_1>0$ solve $\Phi(\underline Q_0)=\frac{p-w}{p-b}$ and $\Phi(\underline Q_1)=\frac{p+u-w}{p+u-b}$, and let $\tau$ be the threshold of the no-effort problem with $b$ in place of $s$. Fix an effort level $e\ge 0$ and put $Q_2=e\underline Q_0$, $Q_3=e\underline Q_1$. The set $Q^*$ of maximizers of $Q\mapsto R(Q,e\mid T)$ over $Q\ge0$ is
--   $$Q^*=\begin{cases}\{Q_2\} & \text{if } e<T/\tau,\\ \{Q_3\} & \text{if } e>T/\tau,\\ \{Q_2,Q_3\} & \text{if } e=T/\tau.\end{cases}$$
--
--   The lemma reduces the retailer's two-variable problem to a problem in effort alone.
--
--   **Formalization Note.** The paper states Lemma 2 for a general demand distribution. It is stated here for $\xi\sim\mathrm{Uniform}(0,1)$, the case that Lemmas 3–6 and Theorem 2 use. "Optimal order quantity" is the set of maximizers over $Q\ge0$.
-- source:
--   Taylor, Supply Chain Coordination Under Channel Rebates with Sales Effort Effects, Management Science 48(8) (2002), p. 1000, Lemma 2 (with Q̲₁, Q₃, τ defined just before it; τ₀ from §3.2, p. 995); proof p. 1005

import Mathlib
import Definitions.Def_ChannelRebate_Effort_Setting

open MeasureTheory Filter Topology

namespace ChannelRebate.Effort

theorem lemma2_optimal_order_given_effort
    (p c s w a u b T : ℝ) (hc : 0 < c) (hcw : c < w) (hwp : w < p) (hsc : s < c) (ha : 0 < a)
    (hu : 0 < u) (hsb : s ≤ b) (hbw : b < w) (hT : 0 < T)
    (Q0 Q1 τ : ℝ) (hQ0 : IsQlow0 p w b Q0) (hQ1 : IsQlow1 p w u b Q1) (hτ : IsTau p w u b τ)
    (e : ℝ) (he : 0 ≤ e) :
    (e < T / τ → optimalSet (fun Q => R p w u b a T Q e) = {e * Q0}) ∧
      (T / τ < e → optimalSet (fun Q => R p w u b a T Q e) = {e * Q1}) ∧
      (e = T / τ → optimalSet (fun Q => R p w u b a T Q e) = {e * Q0, e * Q1}) := by sorry

end ChannelRebate.Effort
