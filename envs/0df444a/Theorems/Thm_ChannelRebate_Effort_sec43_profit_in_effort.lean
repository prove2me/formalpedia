-- Prove2me | Theorems.Thm_ChannelRebate_Effort_sec43_profit_in_effort
-- name    : ChannelRebate.Effort.sec43_profit_in_effort
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:13:18.827524+00:00
-- url     : https://prove2.me/theorems/6e920519-3748-453e-96b4-0434c6ee87cf
-- title:
--   §4.3, p. 1001 — A(e|T) has the two-branch formula, a kink at T/τ with left derivative < right derivative, so T/τ is never optimal
-- statement:
--   In the setting of Lemma 2 ($0<c<w<p$, $s<c$, $a>0$, $u>0$, $b\in[s,w)$, $T>0$, $\xi\sim\mathrm{Uniform}(0,1)$, $V(e)=ae^2/2$), let $A(e\mid T)=\max_{Q\ge0}R(Q,e\mid T)$. Then:
--
--   1. the maximum is attained and
--   $$A(e\mid T)=\begin{cases} e(p-b)\Gamma(\underline Q_0)-V(e) & \text{if } 0\le e\le T/\tau,\\ e(p+u-b)\Gamma(\underline Q_1)-u\bigl(e\Gamma(T/e)+T[1-\Phi(T/e)]\bigr)-V(e) & \text{if } e>T/\tau;\end{cases}$$
--   2. for $0<e<T/\tau$, $\frac{\partial}{\partial e}A(e\mid T)=(p-b)\Gamma(\underline Q_0)-V'(e)$, and for $e>T/\tau$, $\frac{\partial}{\partial e}A(e\mid T)=(p+u-b)\Gamma(\underline Q_1)-u\Gamma(T/e)-V'(e)$, where $V'(e)=ae$;
--   3. for $0<e<T/\tau$, $\frac{\partial^2}{\partial e^2}A(e\mid T)=-V''(e)=-a$, and for $e>T/\tau$, $\frac{\partial^2}{\partial e^2}A(e\mid T)=e^{-3}uT^2\phi(T/e)-V''(e)$, where $\phi=\mathbf 1_{[0,1]}$ is the uniform density and $V''(e)=a$;
--   4. $A(\cdot\mid T)$ is continuous on $[0,\infty)$;
--   5. both one-sided limits of the derivative at $T/\tau$ exist and $$\lim_{e\to(T/\tau)^-}\tfrac{\partial}{\partial e}A(e\mid T)<\lim_{e\to(T/\tau)^+}\tfrac{\partial}{\partial e}A(e\mid T);$$
--   6. consequently $T/\tau$ is not a maximizer of $A(\cdot\mid T)$ over $e\ge0$.
--
--   The kink makes $A(\cdot\mid T)$ neither concave nor differentiable, which is why the optimal effort needs Lemmas 3 and 4.
--
--   **Formalization Note.** $A$ is defined as the real supremum of $R(\cdot,e\mid T)$ over $Q\ge0$; item 1 asserts that the supremum is attained. The paper's derivative display uses $e\le T/\tau$ for the lower branch; at $e=T/\tau$ the function has a kink, so the derivative is stated on the open branches and at $T/\tau$ only through the one-sided limits. The second-derivative display is likewise stated on the open branches, as the derivative of `deriv A`.
-- source:
--   Taylor, Supply Chain Coordination Under Channel Rebates with Sales Effort Effects, Management Science 48(8) (2002), p. 1001, §4.3, display of A(e|T), (∂/∂e)A(e|T), (∂²/∂e²)A(e|T) and the one-sided limit inequality; specialised to ξ ∼ Uniform(0, 1), V(e) = ae²/2

import Mathlib
import Definitions.Def_ChannelRebate_Effort_Setting

open MeasureTheory Filter Topology

namespace ChannelRebate.Effort

theorem sec43_profit_in_effort
    (p c s w a u b T : ℝ) (hc : 0 < c) (hcw : c < w) (hwp : w < p) (hsc : s < c) (ha : 0 < a)
    (hu : 0 < u) (hsb : s ≤ b) (hbw : b < w) (hT : 0 < T)
    (Q0 Q1 τ : ℝ) (hQ0 : IsQlow0 p w b Q0) (hQ1 : IsQlow1 p w u b Q1) (hτ : IsTau p w u b τ) :
    (∀ e, 0 ≤ e → e ≤ T / τ →
        IsGreatest ((fun Q => R p w u b a T Q e) '' Set.Ici 0)
          (e * (p - b) * Gam Q0 - V a e)) ∧
      (∀ e, T / τ < e →
        IsGreatest ((fun Q => R p w u b a T Q e) '' Set.Ici 0)
          (e * (p + u - b) * Gam Q1 - u * (e * Gam (T / e) + T * (1 - Phi (T / e))) - V a e)) ∧
      (∀ e, 0 < e → e < T / τ →
        HasDerivAt (Aeff p w u b a T) ((p - b) * Gam Q0 - a * e) e) ∧
      (∀ e, T / τ < e →
        HasDerivAt (Aeff p w u b a T) ((p + u - b) * Gam Q1 - u * Gam (T / e) - a * e) e) ∧
      (∀ e, 0 < e → e < T / τ →
        HasDerivAt (deriv (Aeff p w u b a T)) (-a) e) ∧
      (∀ e, T / τ < e →
        HasDerivAt (deriv (Aeff p w u b a T))
          (u * T ^ 2 * (Set.Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) (T / e) / e ^ 3 - a) e) ∧
      ContinuousOn (Aeff p w u b a T) (Set.Ici 0) ∧
      (∃ Lm Lp : ℝ, Tendsto (deriv (Aeff p w u b a T)) (𝓝[<] (T / τ)) (𝓝 Lm) ∧
        Tendsto (deriv (Aeff p w u b a T)) (𝓝[>] (T / τ)) (𝓝 Lp) ∧ Lm < Lp) ∧
      T / τ ∉ optimalSet (Aeff p w u b a T) := by sorry

end ChannelRebate.Effort
