-- Prove2me | Theorems.Thm_CallNoCall_OneDir_rate_comparison
-- name    : CallNoCall.OneDir.rate_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:05.739806+00:00
-- url     : https://prove2.me/theorems/cc37141d-f177-4402-b9fc-929aa5ed9e84
-- title:
--   Proof of Theorem 4, p. 38 — in every state n ≥ 1 the no-call service rate µ^(nc)_n is at least the call service rate µ^(1c)_n
-- statement:
--   Let $d, v, R > 0$, $k \ge 1$ and $\lambda \ge 0$. For every state $n \ge 1$ the call service rate (1) is positive and does not exceed the no-call service rate (3):
--   $$0 < \mu^{(1c)}_n \le \mu^{(nc)}_n .$$
--
--   So the approximated one-direction no-call system serves at least as fast as the approximated one-direction call system in every system state. Together with the comparison principle for state-dependent $M/M/k$ queues this gives Theorem 4.
--
--   **Formalization Note** The paper prints the strict inequality $\mu^{(nc)}_n > \mu^{(1c)}_n$ "for all $n$". It fails in two cases, where the two rates coincide: $n = k = 1$ (the Gaussian factor is $\exp(0) = 1$ and both en-route times are $R/(2v)$), and $n > k$ when $\lambda = 0$. The weak inequality is stated, which is what Theorem 4's "$\le$" uses. The paper's parenthetical explanation, that $\mu^{(1c)}_n$ is $\mu^{(nc)}_n$ without the exponential factor, is literally true only for $n \ge k$ and is not formalized. Positivity of $\mu^{(1c)}_n$ is the implicit reading of (1) as a rate and is included in the conclusion. The standing assumptions $d, v, R > 0$, $k \ge 1$, $\lambda \ge 0$ are explicit hypotheses.
-- source:
--   Feng, Kong, Wang, We Are on the Way: Analysis of On-Demand Ride-Hailing Systems, SSRN working paper 2960991 (version of 2020-04-16), p. 38, Appendix A, proof of Theorem 4 (first sentence)

import Mathlib
import Definitions.Def_CallNoCall_OneDir_Setting

namespace CallNoCall.OneDir

/-- Proof of Theorem 4, p. 38: in every state `n ≥ 1` the call service rate `μ^{(1c)}_n` is
positive and at most the no-call service rate `μ^{(nc)}_n`. -/
theorem rate_comparison (lam d v R : ℝ) (k : ℕ) (hd : 0 < d) (hv : 0 < v) (hR : 0 < R)
    (hk : 1 ≤ k) (hlam0 : 0 ≤ lam) (n : ℕ) (hn : 1 ≤ n) :
    0 < mu1c d v R k n ∧ mu1c d v R k n ≤ muNC lam d v R k n := by sorry

end CallNoCall.OneDir
