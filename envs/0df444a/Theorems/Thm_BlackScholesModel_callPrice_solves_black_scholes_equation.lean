-- Prove2me | Theorems.Thm_BlackScholesModel_callPrice_solves_black_scholes_equation
-- name    : BlackScholesModel.callPrice_solves_black_scholes_equation
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:39:46.594563+00:00
-- url     : https://prove2.me/theorems/7b9f86c4-ef67-48b5-a89c-e0f23038fec0
-- title:
--   Black–Scholes formula solves the Black–Scholes equation
-- statement:
--   Let $K>0$ be the strike, $T$ the expiry, $r\in\mathbb R$ the risk-free rate and $\sigma>0$ the volatility, and let $C(S,t)=N(d_+)S-N(d_-)Ke^{-r(T-t)}$ be the Black–Scholes call price. Then on the open domain $\{(S,t):S>0,\ t<T\}$:
--
--   1. $C$ is infinitely differentiable in $(S,t)$;
--   2. $C$ satisfies the Black–Scholes equation
--   $$\frac{\partial C}{\partial t}+\frac12\sigma^2S^2\frac{\partial^2C}{\partial S^2}+rS\frac{\partial C}{\partial S}-rC=0;$$
--   3. for each $t<T$, $C(S,t)\to0$ as $S\to0^+$;
--   4. for each $t<T$, $C(S,t)-\big(S-Ke^{-r(T-t)}\big)\to0$ as $S\to\infty$;
--   5. for each $S>0$, $C(S,t)\to\max\{S-K,0\}$ as $t\to T^-$.
--
--   This is the statement that the Black–Scholes formula is the solution of the Black–Scholes equation with the call's terminal and boundary conditions.
--
--   **Formalization Note** The source writes the conditions as $C(0,t)=0$, $C(S,t)\sim S-Ke^{-r(T-t)}$ as $S\to\infty$ and $C(S,T)=\max\{S-K,0\}$. Since the formula is undefined at $S=0$ and $t=T$, these are stated as one-sided limits; the condition at infinity is stated in the (stronger) form that the difference tends to $0$. The PDE uses `deriv`, made meaningful by the smoothness clause 1.
-- source:
--   Wikipedia, "Black–Scholes model" (snapshot supplied as Black–Scholes_model.pdf, 22 pp.), https://en.wikipedia.org/wiki/Black%E2%80%93Scholes_model; p. 3 (Black–Scholes equation; Black–Scholes formula with terminal and boundary conditions), p. 4 (call formula)

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem callPrice_solves_black_scholes_equation (K r σ T : ℝ) (hK : 0 < K) (hσ : 0 < σ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => callPrice K r σ T p.1 p.2)
        {p : ℝ × ℝ | 0 < p.1 ∧ p.2 < T} ∧
    (∀ S t : ℝ, 0 < S → t < T →
      deriv (fun t' => callPrice K r σ T S t') t
        + 1 / 2 * σ ^ 2 * S ^ 2
            * deriv (fun S' => deriv (fun S'' => callPrice K r σ T S'' t) S') S
        + r * S * deriv (fun S' => callPrice K r σ T S' t) S
        - r * callPrice K r σ T S t = 0) ∧
    (∀ t : ℝ, t < T → Tendsto (fun S => callPrice K r σ T S t) (𝓝[>] 0) (𝓝 0)) ∧
    (∀ t : ℝ, t < T →
      Tendsto (fun S => callPrice K r σ T S t - (S - K * Real.exp (-r * (T - t)))) atTop (𝓝 0)) ∧
    (∀ S : ℝ, 0 < S →
      Tendsto (fun t => callPrice K r σ T S t) (𝓝[<] T) (𝓝 (max (S - K) 0))) := by sorry

end BlackScholesModel
