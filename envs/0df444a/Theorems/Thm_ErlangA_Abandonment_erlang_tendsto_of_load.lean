-- Prove2me | Theorems.Thm_ErlangA_Abandonment_erlang_tendsto_of_load
-- name    : ErlangA.Abandonment.erlang_tendsto_of_load
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:03:00.036664+00:00
-- url     : https://prove2.me/theorems/fb7176cb-6d9a-45f6-a590-ae596d1785c7
-- title:
--   Proof of Theorem 1 — if $\lambda_N=N\mu\rho_\infty+o(N)$, $\rho_\infty>1$, then $P_N\{Bl\}\to1-1/\rho_\infty$ and $\limsup P_N\{Ab\}\le1-1/\rho_\infty$
-- statement:
--   Let $\mu>0$, $1<\rho_\infty<\infty$, and let $(\lambda_N)_{N\ge1}$ be arrival rates with
--   $$
--   \lambda_N=N\mu\rho_\infty+o(N),\qquad\text{i.e.}\qquad \frac{\lambda_N-N\mu\rho_\infty}{N}\to0 .
--   $$
--   Let $P_N\{Bl\}=E(\lambda_N/\mu,N)$ be the blocking probability of $M(\lambda_N)/M(\mu)/N/N$, and for any patience rates $0<\theta_N<\infty$ let $P_N\{Ab\}$ be the steady-state abandonment probability of $M(\lambda_N)/M(\mu)/N+M(\theta_N)$. Then
--   $$
--   \lim_{N\to\infty}P_N\{Bl\}=1-\frac1{\rho_\infty}\qquad\text{and}\qquad \limsup_{N\to\infty}P_N\{Ab\}\le1-\frac1{\rho_\infty}.
--   $$
--
--   This is the upper bound of Theorem 1 in the overloaded case.
--
--   **Formalization Note** The $\limsup$ bound is stated in its elementary form: for every $\varepsilon>0$, eventually $P_N\{Ab\}\le1-1/\rho_\infty+\varepsilon$. No positivity of $\lambda_N$ is assumed, since $\lambda_N/N\to\mu\rho_\infty>0$ makes it eventually positive.
-- source:
--   Garnett, Mandelbaum & Reiman, Designing a Call Center with Impatient Customers, M&SOM 4(3), 2002, p. 223, Appendix C, proof of Theorem 1 (the case λ_N = Nμρ_∞ + o(N))

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Erlang
import Definitions.Def_ErlangA_Abandonment_Model
open Filter Topology

namespace ErlangA.Abandonment

/-- p. 223: if `λ_N = Nμρ_∞ + o(N)` with `1 < ρ_∞ < ∞`, then `P_N{Bl} → 1 − 1/ρ_∞`, and
consequently `lim sup P_N{Ab} ≤ 1 − 1/ρ_∞` for any patience rates `0 < θ_N < ∞`. -/
theorem erlang_tendsto_of_load (μ ρ : ℝ) (lam θN : ℕ → ℝ) (hμ : 0 < μ) (hρ : 1 < ρ)
    (hθN : ∀ N : ℕ, 1 ≤ N → 0 < θN N)
    (hload : Tendsto (fun N : ℕ => (lam N - (N : ℝ) * μ * ρ) / (N : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => KellyStochasticNetworks.erlang (lam N / μ) N) atTop
        (𝓝 (1 - 1 / ρ)) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        probAbandon N (lam N) μ (θN N) ≤ 1 - 1 / ρ + ε := by sorry

end ErlangA.Abandonment
