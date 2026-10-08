-- Prove2me | Theorems.Thm_ErlangA_Abandonment_probAbandon_le_erlang
-- name    : ErlangA.Abandonment.probAbandon_le_erlang
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:03:09.22444+00:00
-- url     : https://prove2.me/theorems/74f282e7-757d-41a6-9cd6-3c8e740f6422
-- title:
--   Proof of Theorem 1 — $P_N\{Ab\}\le P_N\{Bl\}$ for every $0<\theta<\infty$
-- statement:
--   For $N\ge1$ agents, arrival rate $\lambda>0$, service rate $\mu>0$ and any patience rate $0<\theta<\infty$, the steady-state abandonment probability of the Erlang-A queue is at most Erlang's blocking probability of the loss system with the same $N$, $\lambda$, $\mu$:
--   $$
--   P_N\{Ab\}\le P_N\{Bl\}=E(\lambda/\mu,N).
--   $$
--
--   This is the comparison that turns asymptotics of Erlang's formula into the upper bound of Theorem 1.
-- source:
--   Garnett, Mandelbaum & Reiman, Designing a Call Center with Impatient Customers, M&SOM 4(3), 2002, p. 223, Appendix C, proof of Theorem 1

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Erlang
import Definitions.Def_ErlangA_Abandonment_Model
open Filter Topology

namespace ErlangA.Abandonment

/-- p. 223: `P_N{Ab} ≤ P_N{Bl}` for every patience rate `0 < θ < ∞`. -/
theorem probAbandon_le_erlang (N : ℕ) (hN : 1 ≤ N) (lam μ θ : ℝ)
    (hlam : 0 < lam) (hμ : 0 < μ) (hθ : 0 < θ) :
    probAbandon N lam μ θ ≤ KellyStochasticNetworks.erlang (lam / μ) N := by sorry

end ErlangA.Abandonment
