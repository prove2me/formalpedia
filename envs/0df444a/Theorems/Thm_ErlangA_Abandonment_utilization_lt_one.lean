-- Prove2me | Theorems.Thm_ErlangA_Abandonment_utilization_lt_one
-- name    : ErlangA.Abandonment.utilization_lt_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:02:38.536136+00:00
-- url     : https://prove2.me/theorems/ef14e7a3-619a-41d3-9abf-761f9e4fa9a0
-- title:
--   Proof of Theorem 1 — agent utilization below one: $\lambda(1-P\{Ab\})<N\mu$
-- statement:
--   Consider the Erlang-A queue with $N\ge1$ agents, arrival rate $\lambda>0$, service rate $\mu>0$ and patience rate $\theta>0$, and let $P\{Ab\}$ be the steady-state probability that an arriving customer abandons. Then
--   $$
--   \lambda\bigl(1-P\{Ab\}\bigr)<N\mu .
--   $$
--
--   The left side is the rate at which work reaches the agents and the right side the maximal rate at which they can process it, so the inequality says that the agents' utilization is strictly below one. In the proof of Theorem 1 it yields the lower bound $\liminf_N P_N\{Ab\}\ge 1-1/\rho_\infty$.
-- source:
--   Garnett, Mandelbaum & Reiman, Designing a Call Center with Impatient Customers, M&SOM 4(3), 2002, p. 223, Appendix C, proof of Theorem 1, first display

import Mathlib
import Definitions.Def_ErlangA_Abandonment_Model
open Filter Topology

namespace ErlangA.Abandonment

/-- App. C, proof of Theorem 1, p. 223, first display: the agents utilization is below one,
`λ (1 − P{Ab}) < Nμ`. -/
theorem utilization_lt_one (N : ℕ) (hN : 1 ≤ N) (lam μ θ : ℝ)
    (hlam : 0 < lam) (hμ : 0 < μ) (hθ : 0 < θ) :
    lam * (1 - probAbandon N lam μ θ) < (N : ℝ) * μ := by sorry

end ErlangA.Abandonment
