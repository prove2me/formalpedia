-- Prove2me | Theorems.Thm_ErlangA_Abandonment_probAbandon_tendsto_erlang
-- name    : ErlangA.Abandonment.probAbandon_tendsto_erlang
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:02:48.744634+00:00
-- url     : https://prove2.me/theorems/698ec5bc-591c-42b9-b3fb-3adb9cfa042b
-- title:
--   Proof of Theorem 1 — $P_N\{Ab\}\to P_N\{Bl\}$ as $\theta\to\infty$
-- statement:
--   Fix $N\ge1$ agents, an arrival rate $\lambda>0$ and a service rate $\mu>0$. Let $P_N\{Ab\}(\theta)$ be the steady-state abandonment probability of the Erlang-A queue $M(\lambda)/M(\mu)/N+M(\theta)$, and let
--   $$
--   P_N\{Bl\}=E(\lambda/\mu,N)=\frac{(\lambda/\mu)^N/N!}{\sum_{j=0}^{N}(\lambda/\mu)^j/j!}
--   $$
--   be Erlang's blocking probability of the loss system $M(\lambda)/M(\mu)/N/N$. Then
--   $$
--   \lim_{\theta\to\infty}P_N\{Ab\}(\theta)=P_N\{Bl\}.
--   $$
--
--   Infinitely impatient customers leave as soon as they would have to wait, which is blocking. Together with property (ii) this gives the upper bound $P_N\{Ab\}\le P_N\{Bl\}$ used in the proof of Theorem 1.
-- source:
--   Garnett, Mandelbaum & Reiman, Designing a Call Center with Impatient Customers, M&SOM 4(3), 2002, p. 223, Appendix C, proof of Theorem 1 (upper bound, first sentence)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Erlang
import Definitions.Def_ErlangA_Abandonment_Model
open Filter Topology

namespace ErlangA.Abandonment

/-- p. 223: the Erlang-B blocking probability `P_N{Bl} = E(λ/μ, N)` of `M(λ)/M(μ)/N/N` is the
limit of `P_N{Ab}` as `θ → ∞`. -/
theorem probAbandon_tendsto_erlang (N : ℕ) (hN : 1 ≤ N) (lam μ : ℝ)
    (hlam : 0 < lam) (hμ : 0 < μ) :
    Tendsto (fun θ : ℝ => probAbandon N lam μ θ) atTop
      (𝓝 (KellyStochasticNetworks.erlang (lam / μ) N)) := by sorry

end ErlangA.Abandonment
