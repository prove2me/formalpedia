-- Prove2me | Theorems.Thm_ErlangA_Abandonment_jagerman_expansion
-- name    : ErlangA.Abandonment.jagerman_expansion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:01:58.385552+00:00
-- url     : https://prove2.me/theorems/de2b0016-61a9-47ab-98cb-08cfd3f616bf
-- title:
--   Equation (10) — Jagerman's asymptotic expansion of Erlang's formula for $\lambda_N=N\mu\rho_\infty$, $\rho_\infty>1$
-- statement:
--   Let $\mu>0$ and $1<\rho_\infty<\infty$, and consider the loss system with $N$ circuits and offered load $\lambda_N/\mu$, where $\lambda_N=N\mu\rho_\infty$. Then its blocking probability $P_N\{Bl\}=E(\lambda_N/\mu,N)$ satisfies, as $N\to\infty$,
--   $$
--   P_N\{Bl\}\sim\left[\frac{\rho_\infty}{\rho_\infty-1}-\frac{\rho_\infty}{(\rho_\infty-1)^3}\,\frac1N+\frac{2\rho_\infty^2+\rho_\infty}{(\rho_\infty-1)^5}\,\frac1{N^2}\right]^{-1},
--   $$
--   where $a_N\sim b_N$ means that $a_N/b_N\to1$.
--
--   The paper quotes this from Jagerman (1974, p. 538) and uses it, through monotonicity of Erlang's formula, to identify $\lim_N P_N\{Bl\}=1-1/\rho_\infty$ in the overloaded regime.
--
--   **Formalization Note** The statement is the literal asymptotic equivalence $\sim$ (Mathlib's `Asymptotics.IsEquivalent`), not an error bound of order $N^{-3}$, which the page does not assert. Because the correction terms vanish, it is equivalent to $P_N\{Bl\}\to(\rho_\infty-1)/\rho_\infty$.
-- source:
--   Garnett, Mandelbaum & Reiman, Designing a Call Center with Impatient Customers, M&SOM 4(3), 2002, p. 223, eq. (10) (citing Jagerman 1974, p. 538)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Erlang
open Filter Topology

namespace ErlangA.Abandonment

/-- (10), p. 223 (Jagerman 1974): for `λ_N = Nμρ_∞` with `1 < ρ_∞ < ∞`,
`P_N{Bl} ∼ [ρ/(ρ−1) − ρ/(ρ−1)³ · 1/N + (2ρ² + ρ)/(ρ−1)⁵ · 1/N²]⁻¹` (asymptotic equivalence). -/
theorem jagerman_expansion (μ ρ : ℝ) (hμ : 0 < μ) (hρ : 1 < ρ) :
    Asymptotics.IsEquivalent atTop
      (fun N : ℕ => KellyStochasticNetworks.erlang ((N : ℝ) * μ * ρ / μ) N)
      (fun N : ℕ => (ρ / (ρ - 1) - ρ / (ρ - 1) ^ 3 * (1 / (N : ℝ))
        + (2 * ρ ^ 2 + ρ) / (ρ - 1) ^ 5 * (1 / (N : ℝ) ^ 2))⁻¹) := by sorry

end ErlangA.Abandonment
