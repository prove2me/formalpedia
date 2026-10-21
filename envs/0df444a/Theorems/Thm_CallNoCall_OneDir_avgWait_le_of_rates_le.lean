-- Prove2me | Theorems.Thm_CallNoCall_OneDir_avgWait_le_of_rates_le
-- name    : CallNoCall.OneDir.avgWait_le_of_rates_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:18.536868+00:00
-- url     : https://prove2.me/theorems/ecf6b19f-4ffa-4d0e-972d-deffbac5a0da
-- title:
--   Proof of Theorem 4, p. 38 — if every service rate of a state-dependent M/M/k queue increases, the average waiting time stays finite and does not increase
-- statement:
--   Let $\lambda \ge 0$ and let $(\mu_n)_{n\ge1}$ and $(\mu'_n)_{n\ge1}$ be the service rates of two state-dependent $M/M/k$ queues with arrival rate $\lambda$, such that
--   $$0 < \mu_n \le \mu'_n \qquad \text{for every } n \ge 1 .$$
--   If the average waiting time $\mathcal W(\mu)$ is finite, then $\mathcal W(\mu')$ is finite and
--   $$\mathcal W(\mu') \le \mathcal W(\mu).$$
--
--   This is the principle the proof of Theorem 4 announces ("this implies the average waiting time in the no-call system is shorter"): faster service in every state gives a shorter average wait. The paper uses it again in the proofs of Theorem 1(4) and Theorem 5.
--
--   **Formalization Note** The paper derives the principle from the coordinatewise monotonicity of $\mathcal W$ (the preceding milestone) and leaves the passage to infinitely many coordinates implicit; this statement is the conclusion, for all rates at once. $\lambda = 0$ is included: there $\mathcal W(\mu) = 1/\mu_1 - d/v$ (Lean's $0^0 = 1$), and the claim is $1/\mu'_1 \le 1/\mu_1$. "Finite" is the predicate `FiniteWait` (both series summable).
-- source:
--   Feng, Kong, Wang, We Are on the Way: Analysis of On-Demand Ride-Hailing Systems, SSRN working paper 2960991 (version of 2020-04-16), p. 38, Appendix A, proof of Theorem 4

import Mathlib
import Definitions.Def_CallNoCall_OneDir_StateDepQueue

namespace CallNoCall.OneDir

/-- Proof of Theorem 4, p. 38: if every service rate of a state-dependent `M/M/k` queue with
positive rates and finite average waiting time is raised (`μₙ ≤ μ'ₙ` for all `n ≥ 1`), the
average waiting time stays finite and does not increase. -/
theorem avgWait_le_of_rates_le (μ μ' : ℕ → ℝ) (lam d v : ℝ) (hμ : ∀ n, 1 ≤ n → 0 < μ n)
    (hle : ∀ n, 1 ≤ n → μ n ≤ μ' n) (hlam : 0 ≤ lam) (hfin : FiniteWait μ lam) :
    FiniteWait μ' lam ∧ avgWait μ' lam d v ≤ avgWait μ lam d v := by sorry

end CallNoCall.OneDir
