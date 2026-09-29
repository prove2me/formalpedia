-- Prove2me | Theorems.Thm_BertsekasDP_limited_lookahead_bound
-- name    : BertsekasDP.limited_lookahead_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-11T01:41:27.049724+00:00
-- url     : https://prove2.me/theorems/a15ebedc-c4c0-4f24-9850-e321b78c2025
-- title:
--   General lookahead bound with slacks (Prop. 6.3.2)
-- statement:
--   **Proposition 6.3.2 (performance bound with per-stage slacks).** In the basic stochastic model, let $\tilde J_k$ be arbitrary functions with $\tilde J_N = g_N$, and let $\bar\pi$ be an admissible policy which at every stage falls short of the approximation by at most $\delta_k$ (Eq. (6.23)):
--
--   $$\mathbb{E}_w\Bigl[g_k\bigl(x,\bar\mu_k(x),w\bigr) + \tilde J_{k+1}\bigl(f_k(x,\bar\mu_k(x),w)\bigr)\Bigr] \;\le\; \tilde J_k(x) + \delta_k \qquad \text{for all } x, \; k < N .$$
--
--   Then the cost-to-go of $\bar\pi$ obeys the accumulated bound
--
--   $$J_{\bar\pi,k}(x) \;\le\; \tilde J_k(x) \;+\; \sum_{i=k}^{N-1} \delta_i \qquad \text{for all } x \text{ and } k \le N .$$
--
--   Unlike Prop. 6.3.1 this needs no assumption relating $\tilde J$ to a minimization, which makes it the tool of choice when the lookahead minimization is inexact, when the approximation architecture is imperfect, or when the policy comes from elsewhere entirely. The source uses it to bound the certainty equivalent controller, where $\delta_k$ measures the error committed by fixing the disturbance at a nominal value; when every $\delta_k \le 0$ it recovers $J_{\bar\pi,k} \le \tilde J_k$.
--
--   **Formalization Note** The scalars $\delta_k$ carry no sign restriction. No minimality of $\bar\pi$ over any control set is hypothesized — only the displayed inequality — though the policy is required to be admissible. The sum over the empty range at $k = N$ gives the boundary case $J_{\bar\pi,N} \le g_N$.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Proposition 6.3.2

import Mathlib
import Definitions.Def_BertsekasDPModel

namespace BertsekasDP

theorem limited_lookahead_bound {S C W : Type} [Fintype W]
    (M : BertsekasDPModel S C W)
    (Jt : ℕ → S → ℝ) (hJN : ∀ x, Jt M.N x = M.gN x)
    (δ : ℕ → ℝ)
    (π : ℕ → S → C)
    (hadm : ∀ k x, π k x ∈ M.U k x)
    (hπ : ∀ k, k < M.N → ∀ x,
      ∑ w, M.p k x (π k x) w *
          (M.g k x (π k x) w + Jt (k + 1) (M.f k x (π k x) w)) ≤
        Jt k x + δ k) :
    ∀ k, k ≤ M.N → ∀ x,
      BertsekasDPPolicyCost M π (M.N - k) x ≤
        Jt k x + ∑ i ∈ Finset.Ico k M.N, δ i := by sorry

end BertsekasDP
