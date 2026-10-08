-- Prove2me | Theorems.Thm_ErlangA_Abandonment_probAbandon_monotone_arrival
-- name    : ErlangA.Abandonment.probAbandon_monotone_arrival
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:02:35.066804+00:00
-- url     : https://prove2.me/theorems/b369474b-997b-480b-834d-f011d9099c82
-- title:
--   Property (i) — $P_N\{Ab\}$ is increasing in the arrival rate $\lambda$
-- statement:
--   Fix $N\ge1$ agents, a service rate $\mu>0$ and a patience rate $\theta>0$, and let $P_N\{Ab\}(\lambda)$ be the steady-state abandonment probability of the Erlang-A queue with arrival rate $\lambda$. Then
--   $$
--   0<\lambda_1\le\lambda_2\ \Longrightarrow\ P_N\{Ab\}(\lambda_1)\le P_N\{Ab\}(\lambda_2).
--   $$
--   Equivalently, $P_N\{Ab\}$ is increasing in the traffic intensity $\rho=\lambda/(N\mu)$.
--
--   The paper quotes this property from Bhattacharya and Ephremides (1991) and uses it to reduce the case $\rho_\infty\le1$ of Theorem 1 to the overloaded case $\rho_\infty=1+\varepsilon$.
--
--   **Formalization Note** "Increasing" is read as nondecreasing; the proof of Theorem 1 uses only this.
-- source:
--   Garnett, Mandelbaum & Reiman, Designing a Call Center with Impatient Customers, M&SOM 4(3), 2002, p. 223, Appendix C, proof of Theorem 1, property (i) (from Bhattacharya and Ephremides 1991)

import Mathlib
import Definitions.Def_ErlangA_Abandonment_Model
open Filter Topology

namespace ErlangA.Abandonment

/-- p. 223, property (i): with `N`, `θ`, `μ` fixed, `P_N{Ab}` is (weakly) increasing in the
arrival rate `λ > 0` (equivalently in `ρ = λ/(Nμ)`). -/
theorem probAbandon_monotone_arrival (N : ℕ) (hN : 1 ≤ N) (μ θ : ℝ)
    (hμ : 0 < μ) (hθ : 0 < θ) :
    MonotoneOn (fun lam : ℝ => probAbandon N lam μ θ) (Set.Ioi 0) := by sorry

end ErlangA.Abandonment
