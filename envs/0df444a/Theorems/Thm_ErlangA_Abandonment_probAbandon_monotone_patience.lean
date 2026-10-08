-- Prove2me | Theorems.Thm_ErlangA_Abandonment_probAbandon_monotone_patience
-- name    : ErlangA.Abandonment.probAbandon_monotone_patience
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:04:40.106063+00:00
-- url     : https://prove2.me/theorems/c90e793d-a7b2-4053-a311-f51fdfdb7d58
-- title:
--   Property (ii) — $P_N\{Ab\}$ is increasing in the abandonment rate $\theta$
-- statement:
--   Fix $N\ge1$ agents, an arrival rate $\lambda>0$ and a service rate $\mu>0$, and let $P_N\{Ab\}(\theta)$ be the steady-state abandonment probability of the Erlang-A queue with patience rate $\theta$. Then
--   $$
--   0<\theta_1\le\theta_2\ \Longrightarrow\ P_N\{Ab\}(\theta_1)\le P_N\{Ab\}(\theta_2).
--   $$
--
--   More impatient customers abandon more often. The paper quotes this property from Bhattacharya and Ephremides (1991) and uses it to compare the Erlang-A queue with the loss system obtained as $\theta\to\infty$.
--
--   **Formalization Note** "Increasing" is read as nondecreasing; the proof of Theorem 1 uses only this.
-- source:
--   Garnett, Mandelbaum & Reiman, Designing a Call Center with Impatient Customers, M&SOM 4(3), 2002, p. 223, Appendix C, proof of Theorem 1, property (ii) (from Bhattacharya and Ephremides 1991)

import Mathlib
import Definitions.Def_ErlangA_Abandonment_Model
open Filter Topology

namespace ErlangA.Abandonment

/-- p. 223, property (ii): with `N`, `μ`, `λ` fixed, `P_N{Ab}` is (weakly) increasing in the
patience rate `θ > 0`. -/
theorem probAbandon_monotone_patience (N : ℕ) (hN : 1 ≤ N) (lam μ : ℝ)
    (hlam : 0 < lam) (hμ : 0 < μ) :
    MonotoneOn (fun θ : ℝ => probAbandon N lam μ θ) (Set.Ioi 0) := by sorry

end ErlangA.Abandonment
