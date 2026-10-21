-- Prove2me | Theorems.Thm_CallNoCall_OneDir_theorem_4
-- name    : CallNoCall.OneDir.theorem_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:12.983955+00:00
-- url     : https://prove2.me/theorems/ddf5ea48-f777-4d4c-92f9-fbba66e9fb34
-- title:
--   Theorem 4, p. 21 — in the one-direction approximations the no-call average waiting time is at most the call average waiting time
-- statement:
--   Let $d, v, R > 0$ (mean ride distance, speed, perimeter of the circular road), let $k \ge 1$ be the number of taxis, and let the arrival rate satisfy
--   $$0 \le \lambda < \frac{kv}{d}.$$
--   Then the approximated one-direction call system (service rates (1)) and the approximated no-call system (service rates (3)) both have finite average waiting time, and
--   $$\mathcal W^{(nc)}(\lambda,d,v,k,R) \le \mathcal W^{(1c)}(\lambda,d,v,k,R).$$
--
--   In the one-direction approximation, street-hailing (a passenger is picked up by the first free taxi passing by) never has a longer average wait than on-demand matching (each passenger is matched at once to the nearest available taxi). The paper explains this by the no-call mechanism expediting the next pick-up in every state, and confirms it numerically in Figure 11(a).
--
--   **Formalization Note** The paper states the theorem "for any $\lambda$, $d$, $v$, $k$ and $R$". The physical domain $d, v, R > 0$, $k \ge 1$, $\lambda \ge 0$ is made explicit. For $\lambda \ge kv/d$ both waiting times are $+\infty$ (for the call system by Theorem 1(1); for the no-call system because $\mu^{(nc)}_n \le \min\{n,k\}\,v/d$, p. 38), so the inequality there reads $\infty \le \infty$ and has no content; the theorem is stated on the stability region $\lambda < kv/d$, with the real-valued waiting times, and both systems' finiteness (`FiniteWait`) is part of the conclusion. The conclusion is the theorem's "$\le$"; the strict "$\mathcal W^{(nc)} < \mathcal W^{(1c)}$" at the end of the proof (p. 39) fails at $\lambda = 0$, $k = 1$, where both equal $R/(2v)$. $\mathcal W^{(1c)}$ and $\mathcal W^{(nc)}$ are the closed-form waiting times of the $M/M/k$ approximations, not of the simulated systems.
-- source:
--   Feng, Kong, Wang, We Are on the Way: Analysis of On-Demand Ride-Hailing Systems, SSRN working paper 2960991 (version of 2020-04-16), p. 21, Theorem 4; proof in Appendix A, pp. 38–39

import Mathlib
import Definitions.Def_CallNoCall_OneDir_Setting

namespace CallNoCall.OneDir

/-- Theorem 4, p. 21: for every arrival rate `0 ≤ λ < kv/d` (the region where both waiting times
are finite) and every `d, v, R > 0`, `k ≥ 1`, both approximated one-direction systems have finite
average waiting time and `W^{(nc)}(λ,d,v,k,R) ≤ W^{(1c)}(λ,d,v,k,R)`. -/
theorem theorem_4 (lam d v R : ℝ) (k : ℕ) (hd : 0 < d) (hv : 0 < v) (hR : 0 < R) (hk : 1 ≤ k)
    (hlam0 : 0 ≤ lam) (hlam : lam < k * v / d) :
    FiniteWait (mu1c d v R k) lam ∧ FiniteWait (muNC lam d v R k) lam ∧
      Wnc lam d v R k ≤ W1c lam d v R k := by sorry

end CallNoCall.OneDir
