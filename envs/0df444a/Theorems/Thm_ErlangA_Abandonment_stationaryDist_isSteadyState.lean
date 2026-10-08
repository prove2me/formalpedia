-- Prove2me | Theorems.Thm_ErlangA_Abandonment_stationaryDist_isSteadyState
-- name    : ErlangA.Abandonment.stationaryDist_isSteadyState
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:02:39.091104+00:00
-- url     : https://prove2.me/theorems/7bb06c8d-3d00-4a58-855f-ba655895b161
-- title:
--   Appendix B — the explicit $\pi$ is the unique stationary distribution of the Erlang-A queue
-- statement:
--   Consider the Erlang-A queue with $N\ge1$ agents, arrival rate $\lambda>0$, service rate $\mu>0$ and patience rate $\theta>0$: the birth–death process with birth rate $\lambda$ and death rates $\mu_k=\min(k,N)\mu+(k-N)^+\theta$. Let
--   $$
--   \pi_k=\begin{cases}\dfrac{(\lambda/\mu)^k}{k!}\,\pi_0, & 0\le k\le N,\\[2mm] \displaystyle\prod_{j=N+1}^{k}\frac{\lambda}{N\mu+(j-N)\theta}\cdot\frac{(\lambda/\mu)^N}{N!}\,\pi_0, & k>N,\end{cases}
--   $$
--   with $\pi_0$ chosen so that $\sum_k\pi_k=1$. Then $(\pi_k)_{k\ge0}$ is a steady-state distribution of the process: $\pi_k\ge0$, $\sum_k\pi_k=1$, and the global balance equations
--   $$
--   (\lambda+\mu_n)\pi_n=\lambda\pi_{n-1}+\mu_{n+1}\pi_{n+1}\ (n\ge1),\qquad \lambda\pi_0=\mu_1\pi_1
--   $$
--   hold. Moreover it is the only probability distribution solving these equations.
--
--   In particular the normalizing series converges for every $\theta>0$, so all performance measures defined from $\pi$ are genuine.
--
--   **Formalization Note** The paper states the formula for a buffer of size $B$ and introduces $\pi$ as $\lim_{t\to\infty}P\{Q(t)=n\}$; the case $B=\infty$ used throughout §4 is formalized, and "stationary" is read as the steady-state (balance-equation) solution of the published definition `QueueingFundamentals.BirthDeath.IsSteadyState`; the time-limit reading would need a Markov process and is not formalized.
-- source:
--   Garnett, Mandelbaum & Reiman, Designing a Call Center with Impatient Customers, M&SOM 4(3), 2002, pp. 221–222, Appendix B, stationary distribution π_k (case B = ∞)

import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Balance
import Definitions.Def_ErlangA_Abandonment_Model
open Filter Topology

namespace ErlangA.Abandonment

/-- App. B, pp. 221–222 (`B = ∞`): for `N ≥ 1` agents and `λ, μ, θ > 0`, the explicit `π` is a
steady state of the Erlang-A birth–death process (nonnegative, summing to one, global balance),
and it is the only one. -/
theorem stationaryDist_isSteadyState (N : ℕ) (hN : 1 ≤ N) (lam μ θ : ℝ)
    (hlam : 0 < lam) (hμ : 0 < μ) (hθ : 0 < θ) :
    QueueingFundamentals.BirthDeath.IsSteadyState (fun _ => lam) (deathRate N μ θ)
        (stationaryDist N lam μ θ) ∧
      ∀ p : ℕ → ℝ, QueueingFundamentals.BirthDeath.IsSteadyState (fun _ => lam)
          (deathRate N μ θ) p → p = stationaryDist N lam μ θ := by sorry

end ErlangA.Abandonment
