-- Prove2me | Theorems.Thm_ErlangA_Staffing_riordan_identity
-- name    : ErlangA.Staffing.riordan_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:09:00.776177+00:00
-- url     : https://prove2.me/theorems/33fec4b4-30ae-46e1-a67f-283b2b35690a
-- title:
--   Proof of Lemma 2 — Riordan's identity for $P_N\{Ab\}$ via the incomplete gamma function
-- statement:
--   Fix $N\ge1$ agents, arrival rate $\lambda>0$, service rate $\mu>0$ and patience rate $\theta>0$, and let $\rho=\lambda/(N\mu)$. For the stationary Erlang-A queue,
--   $$
--   P_N\{Ab\}=\Bigl(1-\frac1{\rho}+\frac{(\lambda/\theta)^{N\mu/\theta-1}e^{-\lambda/\theta}}{\gamma(N\mu/\theta,\lambda/\theta)}\Bigr)P_N\{W>0\},
--   $$
--   where $\gamma(x,y)=\int_0^y t^{x-1}e^{-t}\,dt$ is the lower incomplete gamma function.
--
--   This is the balance equation $P_N\{Ab\}=\theta E[W\mid W>0]P_N\{W>0\}$ with Riordan's (1962) closed form for the conditional mean wait; it expresses $P_N\{Ab\}$ through $P_N\{W>0\}$ exactly, for every $N$.
--
--   **Formalization Note** The page prints $(\lambda_N\theta)^{N\mu/\theta-1}$; the identity holds with $(\lambda_N/\theta)^{N\mu/\theta-1}$ (checked numerically to 40 digits at several parameter points, while the printed form fails), and the corrected identity is stated. The power is a real power.
-- source:
--   Garnett, Mandelbaum & Reiman, Designing a Call Center with Impatient Customers, M&SOM 4(3), 2002, p. 226, Appendix C, proof of Lemma 2, Riordan display (misprint (λ_Nθ) corrected to (λ_N/θ)); γ from Appendix B, p. 222

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Erlang
import Definitions.Def_DimCallCenters_Rationalized_delayFn
import Definitions.Def_ErlangA_Staffing_Model
open Filter Topology DimCallCenters.Rationalized

namespace ErlangA.Staffing

/-- **Riordan identity** (proof of Lemma 2, p. 226; the printed `(λ_Nθ)` corrected to `(λ_N/θ)`).
For `N ≥ 1` agents and `λ, μ, θ > 0`, with `ρ = λ/(Nμ)`:
`P_N{Ab} = (1 − 1/ρ + (λ/θ)^{Nμ/θ − 1} e^{−λ/θ} / γ(Nμ/θ, λ/θ)) · P_N{W > 0}`. -/
theorem riordan_identity (N : ℕ) (lam μ θ : ℝ) (hN : 1 ≤ N) (hlam : 0 < lam) (hμ : 0 < μ)
    (hθ : 0 < θ) :
    ErlangA.Abandonment.probAbandon N lam μ θ =
      (1 - 1 / (lam / ((N : ℝ) * μ)) +
        (lam / θ) ^ ((N : ℝ) * μ / θ - 1) * Real.exp (-(lam / θ)) /
          lowerGamma ((N : ℝ) * μ / θ) (lam / θ)) * probWait N lam μ θ := by sorry

end ErlangA.Staffing
