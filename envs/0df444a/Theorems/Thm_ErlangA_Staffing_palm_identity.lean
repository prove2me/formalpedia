-- Prove2me | Theorems.Thm_ErlangA_Staffing_palm_identity
-- name    : ErlangA.Staffing.palm_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:09:04.998963+00:00
-- url     : https://prove2.me/theorems/6ff6d32c-1e3f-4f21-aa39-21278064b960
-- title:
--   Proof of Lemma 2 — Palm's identity: $P_N\{Ab\}$ through $P_N\{Bl\}$, $\pi_N$ and $P_N\{W>0\}$
-- statement:
--   Fix $N\ge1$ agents, arrival rate $\lambda>0$, service rate $\mu>0$ and patience rate $\theta>0$; let $\rho=\lambda/(N\mu)$, let $\pi_N$ be the stationary probability that exactly $N$ customers are in the Erlang-A system, and let $P_N\{Bl\}=E(\lambda/\mu,N)$ be the Erlang-B blocking probability. Then
--   $$
--   P_N\{Ab\}=\Bigl(1-\frac1{\rho}+\frac{P_N\{Bl\}/\rho}{P_N\{Bl\}/\pi_N-1+P_N\{Bl\}}\Bigr)\cdot P_N\{W>0\}.
--   $$
--
--   The identity is exact for every $N$ and rewrites the incomplete-gamma term of Riordan's formula in terms of the loss system $M/M/N/N$, whose asymptotics are classical.
-- source:
--   Garnett, Mandelbaum & Reiman, Designing a Call Center with Impatient Customers, M&SOM 4(3), 2002, p. 226, Appendix C, proof of Lemma 2, Palm display

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Erlang
import Definitions.Def_DimCallCenters_Rationalized_delayFn
import Definitions.Def_ErlangA_Staffing_Model
open Filter Topology DimCallCenters.Rationalized

namespace ErlangA.Staffing

/-- **Palm identity** (proof of Lemma 2, p. 226). For `N ≥ 1` agents and `λ, μ, θ > 0`, with
`ρ = λ/(Nμ)`, `P_N{Bl}` the Erlang-B probability and `π_N` the stationary probability of state `N`:
`P_N{Ab} = (1 − 1/ρ + (P_N{Bl}/ρ)/(P_N{Bl}/π_N − 1 + P_N{Bl})) · P_N{W > 0}`. -/
theorem palm_identity (N : ℕ) (lam μ θ : ℝ) (hN : 1 ≤ N) (hlam : 0 < lam) (hμ : 0 < μ)
    (hθ : 0 < θ) :
    ErlangA.Abandonment.probAbandon N lam μ θ =
      (1 - 1 / (lam / ((N : ℝ) * μ)) +
        (probBlock N lam μ / (lam / ((N : ℝ) * μ))) /
          (probBlock N lam μ / ErlangA.Abandonment.stationaryDist N lam μ θ N - 1 + probBlock N lam μ)) *
        probWait N lam μ θ := by sorry

end ErlangA.Staffing
