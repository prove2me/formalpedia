-- Prove2me | Theorems.Thm_CallNoCall_OneDir_theorem_1_1
-- name    : CallNoCall.OneDir.theorem_1_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:58.736392+00:00
-- url     : https://prove2.me/theorems/215ce25f-1a74-48cc-ae7a-208807565f55
-- title:
--   Theorem 1(1), p. 16 — the one-direction call approximation has finite average waiting time iff 0 ≤ λ < kv/d
-- statement:
--   Let $d, v, R > 0$, let $k \ge 1$ be the number of taxis, and let $\lambda \ge 0$ be the arrival rate. Consider the approximated one-direction call system, the state-dependent $M/M/k$ queue with arrival rate $\lambda$ and service rates $\mu^{(1c)}_n$ of (1). Its average waiting time $\mathcal W^{(1c)}(\lambda,d,v,k,R)$ is finite, i.e. both series
--   $$\sum_{i=1}^{\infty} \frac{i\lambda^{i-1}}{\mu^{(1c)}_1\cdots\mu^{(1c)}_i}, \qquad \sum_{i=1}^{\infty} \frac{\lambda^{i}}{\mu^{(1c)}_1\cdots\mu^{(1c)}_i}$$
--   converge, if and only if
--   $$\lambda < k\mu = \frac{kv}{d}.$$
--
--   This is the stability region of the call system: $k\mu$ is the full service capacity of $k$ busy taxis, and the en-route time keeps every rate $\mu^{(1c)}_n$ strictly below it. In the proof of Theorem 4 it shows that on $0 \le \lambda < kv/d$ the call system's waiting time is a finite number.
--
--   **Formalization Note** "$\mathcal W < \infty$" is the predicate `FiniteWait` (both series summable), as in the paper's proof (p. 34). The paper's "$0 \le \lambda$" is part of the domain of the arrival rate and is taken as the hypothesis $\lambda \ge 0$; the equivalence is then with $\lambda < kv/d$. The standing assumptions $d, v, R > 0$ and $k \ge 1$ are implicit in the paper (a distance, a speed, a perimeter, a number of taxis) and are explicit hypotheses here.
-- source:
--   Feng, Kong, Wang, We Are on the Way: Analysis of On-Demand Ride-Hailing Systems, SSRN working paper 2960991 (version of 2020-04-16), p. 16, Theorem 1(1); proof in Appendix A, p. 34

import Mathlib
import Definitions.Def_CallNoCall_OneDir_Setting

namespace CallNoCall.OneDir

/-- Theorem 1(1), p. 16: for `λ ≥ 0`, the approximated one-direction call system has finite
average waiting time (both series of the waiting-time formula converge) if and only if
`λ < kμ = kv/d`. -/
theorem theorem_1_1 (lam d v R : ℝ) (k : ℕ) (hd : 0 < d) (hv : 0 < v) (hR : 0 < R) (hk : 1 ≤ k)
    (hlam0 : 0 ≤ lam) :
    FiniteWait (mu1c d v R k) lam ↔ lam < k * v / d := by sorry

end CallNoCall.OneDir
