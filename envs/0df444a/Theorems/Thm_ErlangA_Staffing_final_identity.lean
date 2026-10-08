-- Prove2me | Theorems.Thm_ErlangA_Staffing_final_identity
-- name    : ErlangA.Staffing.final_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:08:49.002183+00:00
-- url     : https://prove2.me/theorems/4b9c9814-07dd-45a3-b73e-af4ee989306b
-- title:
--   Proof of Lemma 2 — $P_N\{Ab\}$ as a function of $P_N\{W>0\}$ and $P_N\{Bl\}$ only
-- statement:
--   Fix $N\ge1$ agents, arrival rate $\lambda>0$, service rate $\mu>0$ and patience rate $\theta>0$, let $\rho=\lambda/(N\mu)$ and let $P_N\{Bl\}=E(\lambda/\mu,N)$ be the Erlang-B blocking probability. For the stationary Erlang-A queue,
--   $$
--   P_N\{Ab\}=\Bigl(1-\frac1{\rho}+\frac{P_N\{Bl\}/\rho}{(1-P_N\{Bl\})/(1-P_N\{W>0\})-1+P_N\{Bl\}}\Bigr)\times P_N\{W>0\}.
--   $$
--
--   This exact identity expresses the abandonment probability through two quantities whose square-root-regime limits are known (Lemma 1 and the Erlang-B asymptotics), and multiplying it by $\sqrt N$ yields Lemma 2.
-- source:
--   Garnett, Mandelbaum & Reiman, Designing a Call Center with Impatient Customers, M&SOM 4(3), 2002, p. 226, Appendix C, proof of Lemma 2, final display

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Erlang
import Definitions.Def_DimCallCenters_Rationalized_delayFn
import Definitions.Def_ErlangA_Staffing_Model
open Filter Topology DimCallCenters.Rationalized

namespace ErlangA.Staffing

/-- **Final identity** (proof of Lemma 2, p. 226). For `N ≥ 1` agents and `λ, μ, θ > 0`, with
`ρ = λ/(Nμ)`: `P_N{Ab} = (1 − 1/ρ + (P_N{Bl}/ρ)/((1 − P_N{Bl})/(1 − P_N{W > 0}) − 1 + P_N{Bl}))
× P_N{W > 0}`. -/
theorem final_identity (N : ℕ) (lam μ θ : ℝ) (hN : 1 ≤ N) (hlam : 0 < lam) (hμ : 0 < μ)
    (hθ : 0 < θ) :
    ErlangA.Abandonment.probAbandon N lam μ θ =
      (1 - 1 / (lam / ((N : ℝ) * μ)) +
        (probBlock N lam μ / (lam / ((N : ℝ) * μ))) /
          ((1 - probBlock N lam μ) / (1 - probWait N lam μ θ) - 1 + probBlock N lam μ)) *
        probWait N lam μ θ := by sorry

end ErlangA.Staffing
