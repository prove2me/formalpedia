-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_doubling_phase_visit_sum_le
-- name    : BanditAlgorithm.mdp_doubling_phase_visit_sum_le
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-02T03:43:07.951809+00:00
-- url     : https://prove2.me/theorems/a8adde3f-4da8-4d12-ad67-fa42c3a672b5
-- title:
--   Doubling rule: $\sum_k c_k/\sqrt{1\vee b_k}\le(\sqrt2+1)\sqrt{n}$
-- statement:
--   Let $b, c : \mathbb{N} \to \mathbb{R}$ satisfy $b_0 = 0$, $c_k \ge 0$, $b_{k+1} = b_k + c_k$, and $c_k \le 1 \vee b_k$. Then for every $K \in \mathbb{N}$,
--
--   $$\sum_{k < K} \frac{c_k}{\sqrt{1 \vee b_k}} \;\le\; (\sqrt{2} + 1)\,\sqrt{b_K}.$$
--
--   This is Exercise 38.22 of Lattimore and Szepesvári, the discrete counterpart of the integral $\int_0^K \frac{f'(k)}{\sqrt{f(k)}}\,dk = 2\sqrt{f(K)} - 2\sqrt{f(0)}$ of Eq. (38.21). It is the key counting step of Step 3 in the proof of the UCRL2 regret bound (Theorem 38.6): there $b_k = T_{\tau_k - 1}(s,a)$ is the number of visits to a fixed state-action pair before phase $k$ and $c_k = T_{(k)}(s,a)$ is the number of visits during phase $k$, so that $b_{k+1} = b_k + c_k$; the phase rule of UCRL2 — a new phase starts as soon as the visit count of the pair just played has doubled — is exactly the hypothesis $c_k \le 1 \vee b_k$.
--
--   The proof is a single telescoping step. Put $M = 1 \vee b_k$. Both $b_k$ and the increment $c_k$ are at most $M$, so $b_k + c_k \le 2M$ and therefore
--
--   $$\sqrt{b_k + c_k} + \sqrt{b_k} \;\le\; (\sqrt{2}+1)\sqrt{M}.$$
--
--   Multiplying by $\sqrt{b_k + c_k} - \sqrt{b_k} \ge 0$ and using $(\sqrt{b_{k+1}})^2 - (\sqrt{b_k})^2 = c_k$ gives
--
--   $$\frac{c_k}{\sqrt{1 \vee b_k}} \;\le\; (\sqrt{2}+1)\left(\sqrt{b_{k+1}} - \sqrt{b_k}\right),$$
--
--   and summing telescopes to the claim.
--
--   The statement is deliberately phrased for real-valued counts, so that it applies verbatim to the integer visit counts of UCRL2 and to any other doubling schedule.
-- source:
--   Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Exercise 38.22, used in Step 3 of the proof of Theorem 38.6 (UCRL2 regret bound), Eq. (38.21); Jaksch, Ortner & Auer, Near-optimal Regret Bounds for Reinforcement Learning, JMLR 11 (2010), Section 4.3.2.

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

theorem BanditAlgorithm.mdp_doubling_phase_visit_sum_le (b c : ℕ → ℝ)
    (hb0 : b 0 = 0) (hc : ∀ k, 0 ≤ c k) (hstep : ∀ k, b (k + 1) = b k + c k)
    (hdouble : ∀ k, c k ≤ max 1 (b k)) (K : ℕ) :
    ∑ k ∈ Finset.range K, c k / Real.sqrt (max 1 (b k))
      ≤ (Real.sqrt 2 + 1) * Real.sqrt (b K) := by
  sorry
