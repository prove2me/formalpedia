-- Prove2me | Theorems.Thm_ErlangA_Abandonment_abandonment_balance
-- name    : ErlangA.Abandonment.abandonment_balance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:04:42.107585+00:00
-- url     : https://prove2.me/theorems/29e1c58e-b588-4356-889a-7f314c0fc781
-- title:
--   Equation (2) — $\theta\,E[\#\text{waiting}] = \lambda\,P\{Ab\}$ in the Erlang-A queue
-- statement:
--   Consider the Erlang-A queue with $N\ge1$ agents, arrival rate $\lambda>0$, service rate $\mu>0$ and patience rate $\theta>0$, with stationary distribution $\pi$ of the number in system and abandonment probability $P\{Ab\}$ of an arriving customer. The number of customers waiting in queue is $(Q-N)^+$. Then its stationary mean is finite and
--   $$
--   \theta\cdot E[\#\text{ waiting in queue}]=\theta\sum_{k\ge0}(k-N)^+\pi_k=\lambda\cdot P\{Ab\}.
--   $$
--
--   This is the balance between the rate at which customers abandon the queue and the rate at which customers who will eventually abandon enter the system; the paper uses it to estimate $\theta$ from averaged call-center data.
--
--   **Formalization Note** The statement is a `HasSum`, so it also asserts that $\sum_k (k-N)^+\pi_k$ converges. The paper notes that (2) holds exactly under exponential patience, which is the model here.
-- source:
--   Garnett, Mandelbaum & Reiman, Designing a Call Center with Impatient Customers, M&SOM 4(3), 2002, p. 217, eq. (2)

import Mathlib
import Definitions.Def_ErlangA_Abandonment_Model
open Filter Topology

namespace ErlangA.Abandonment

/-- (2), p. 217: `θ · E[# waiting in queue] = λ · P{Ab}` in steady state, where the number
waiting is `(Q − N)⁺`. The `HasSum` asserts that the mean queue length is finite. -/
theorem abandonment_balance (N : ℕ) (hN : 1 ≤ N) (lam μ θ : ℝ)
    (hlam : 0 < lam) (hμ : 0 < μ) (hθ : 0 < θ) :
    HasSum (fun k : ℕ => θ * (((k - N : ℕ) : ℝ) * stationaryDist N lam μ θ k))
      (lam * probAbandon N lam μ θ) := by sorry

end ErlangA.Abandonment
