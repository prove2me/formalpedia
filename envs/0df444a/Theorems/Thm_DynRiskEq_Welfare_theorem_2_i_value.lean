-- Prove2me | Theorems.Thm_DynRiskEq_Welfare_theorem_2_i_value
-- name    : DynRiskEq.Welfare.theorem_2_i_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:26:36.601523+00:00
-- url     : https://prove2.me/theorems/8f0217bb-6ca0-4aeb-b489-612224921bde
-- title:
--   Theorem 2(i), p. 13 — value identity: a solution of AE_a gives θ_a(n) = max over D_a(n), attained at μ̄ = Σ_k γ^k p^k_a
-- statement:
--   Fix the market data, an agent $a$ with risk generators $p^k_a(n)$, prices $(\pi,\alpha,\mu)$, and suppose $(u_a,x_a,W_a,\theta_a,\gamma)$ solves $\mathrm{AE}_a(\pi,\alpha,\mu,\mathcal D_a)$, the system (20a)–(20g). Then for every non-leaf node $n$,
--   $$\theta_a(n)=\max_{\mu'\in\mathcal D_a(n)}\sum_{m\in n_+}\mu'(m)\big(Z_a(m;u,x,W)-W_a(m)+\theta_a(m)\big)=\sum_{m\in n_+}\bar\mu(m)\big(Z_a(m;u,x,W)-W_a(m)+\theta_a(m)\big),$$
--   where $\bar\mu(m)=\sum_{k\in\mathcal K_a(n)}\gamma^k(n)p^k_a(m)$ and $Z_a$ is the disbenefit (18).
--
--   So the multiplier $\theta_a(n)$ in the complementarity form of the agent's problem is the agent's one-step risk-adjusted cost-to-go, and the convex combination of generators weighted by $\gamma$ is a worst-case measure. Summed over agents, this is the first step of the proof of the First Welfare Theorem.
--
--   **Formalization Note.** This is the value identity of Theorem 2(i) only; its first assertion (that a solution of $\mathrm{AE}_a$ solves the optimization problem $\mathrm{AO}_a$) is not formalized. "max" is stated as `IsGreatest`: $\theta_a(n)$ is attained in, and bounds, the set of values over $\mathcal D_a(n)$, whose elements are functions on the children of $n$. No probability hypothesis on the generators is needed.
-- source:
--   Ferris & Philpott, Dynamic risked equilibrium, author's manuscript of April 16, 2018 (Oper. Res. 2022, doi:10.1287/opre.2019.1958), p. 13, Theorem 2(i) (value identity)

import Mathlib
import Definitions.Def_DynRiskEq_Welfare_Model

open StochasticProg.Multistage FirstOrderOpt.ConvexTheory
open scoped RealInnerProductSpace

namespace DynRiskEq.Welfare

/-- Theorem 2(i), value identity (p. 13). If `(u_a, x_a, W_a, θ_a, γ)` solves
`AE_a(π, α, μ, 𝒟_a)`, then at every non-leaf node `n` the value `θ_a(n)` is the maximum over
`𝒟_a(n)` of `Σ_{m ∈ n+} μ(m)(Z_a(m; u, x, W) − W_a(m) + θ_a(m))`, attained at
`μ̄(m) = Σ_k γ^k(n) p^k_a(m)`. -/
theorem theorem_2_i_value {H : ℕ} (T : Tree H) {A : Type} [Fintype A] [DecidableEq A]
    (M : Market T A) (K : T.Node → ℕ) (p : (n : T.Node) → Fin (K n) → T.Node → ℝ)
    (π : T.Node → ℝ) (α : (a : A) → T.Node → Vec (M.dX a)) (μ : T.Node → ℝ)
    (u : (a : A) → T.Node → Vec (M.dU a)) (x : (a : A) → T.Node → Vec (M.dX a))
    (W : A → T.Node → ℝ) (θa : A → T.Node → ℝ) (a : A) (γ : (n : T.Node) → Fin (K n) → ℝ)
    (hAE : AE T M K p π α μ u x W θa a γ) :
    ∀ n, ¬ IsLeaf T n →
      IsGreatest
        ((fun ν : ↥(T.children n) → ℝ =>
            ∑ m : ↥(T.children n), ν m * (Z T M π α μ u x W a m - W a m + θa a m)) ''
          riskSet T K p n)
        (θa a n) ∧
      θa a n = ∑ m ∈ T.children n,
        (∑ k, γ n k * p n k m) * (Z T M π α μ u x W a m - W a m + θa a m) := by sorry

end DynRiskEq.Welfare
