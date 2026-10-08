-- Prove2me | Theorems.Thm_BellmanDP_Variational_discrete_example_structure
-- name    : BellmanDP.Variational.discrete_example_structure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T19:36:50.521244+00:00
-- url     : https://prove2.me/theorems/70540689-7cbb-4bab-b0e5-972682a707bc
-- title:
--   Chapter IX, Theorem 1 — structure of the optimal policy for the discrete example
-- statement:
--   Let $b$ satisfy Bellman's conditions (10.4) — $b(0)=0$, $b'(0)=\infty$, $b'>0$, $b'(y)\to 0$ as $y\to\infty$, $b''<0$ — and let $u_N$ be defined by
--   $$u_0(c)=c,\qquad u_{N+1}(c)=\max_{0\le v\le c}\bigl[c-v+u_N(c+b(v))\bigr].$$
--   Then there are functions $v_N(c)$ and numbers $c_N$ such that for every $N\ge 1$:
--
--   1. $v_N(c)$ is monotone decreasing as $c\ge 0$ increases;
--   2. $v_{N+1}(c)>v_N(c)$ for all $c\ge 0$;
--   3. the equation $v_N(c)=c$ has a unique solution $c_N\ge 0$, and $c_{N+1}>c_N$;
--   4. for $0\le c\le c_N$, $u_N(c)=u_{N-1}(c+b(c))$, i.e. the optimal choice is $v=c$;
--   5. for $c\ge c_N$, $v_N(c)\ge 0$ and $u_N(c)=c-v_N(c)+u_{N-1}\bigl(c+b(v_N(c))\bigr)$;
--   6. $u_N'(c)\ge u_{N-1}'(c)$ for $c\ge 0$.
--
--   The theorem describes the optimal policy of the discrete process: invest everything ($v=c$) below the threshold $c_N$, and the interior amount $v_N(c)$ above it, with thresholds increasing in the number of remaining stages. It is the discrete counterpart of the transition curve of § 10.
--
--   **Formalization Note** "Monotone decreasing" in (a) is read non-strictly: for $N=1$ the interior optimum $v_1(c)$ solves $b'(v)=1$ and does not depend on $c$, so the strict reading is false. The requirement $v_N(c)\ge 0$ in (e) makes $v_N(c)$ a feasible choice (together with (a) and (c) it gives $0\le v_N(c)\le c$ for $c\ge c_N$); the book's "i.e. $v=c$" treats $v_N$ as the optimal choice. The book presupposes differentiability in (f); the inequality is stated at the points where both $u_N$ and $u_{N-1}$ are differentiable (at $c=0$, $u_N'(0)$ is infinite because $b'(0)=\infty$). The book leaves the proof to the reader.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter IX, Theorem 1, pp. 258-259

import Mathlib
import Definitions.Def_BellmanDP_Variational_DiscreteExample

namespace BellmanDP.Variational

open Set

/-- Bellman, *Dynamic Programming*, Ch. IX, Theorem 1, pp. 258–259. Let `b` satisfy (10.4) and let
`u_N` be given by (11.4). There are functions `v_N (c)` and numbers `c_N` such that for each `N ≥ 1`:
(a) `v_N (c)` is monotone decreasing (non-strictly) in `c ≥ 0`;
(b) `v_{N+1} (c) > v_N (c)` for `c ≥ 0`;
(c) `v_N (c) = c` has a unique solution `c_N ≥ 0`, and `c_{N+1} > c_N`;
(d) for `0 ≤ c ≤ c_N`, `u_N (c) = u_{N−1} (c + b (c))`, i.e. `v = c`;
(e) for `c_N ≤ c`, `v_N (c) ≥ 0` and `u_N (c) = c − v_N (c) + u_{N−1} (c + b (v_N (c)))`;
(f) `u_N′ (c) ≥ u_{N−1}′ (c)` for `c ≥ 0` wherever both derivatives exist. -/
theorem discrete_example_structure (b : ℝ → ℝ) (hb : IsGainFunction b) :
    ∃ (v : ℕ → ℝ → ℝ) (cN : ℕ → ℝ), ∀ N : ℕ, 1 ≤ N →
      AntitoneOn (v N) (Ici 0) ∧
      (∀ c : ℝ, 0 ≤ c → v N c < v (N + 1) c) ∧
      (0 ≤ cN N ∧ v N (cN N) = cN N ∧ (∀ c : ℝ, 0 ≤ c → v N c = c → c = cN N) ∧
        cN N < cN (N + 1)) ∧
      (∀ c : ℝ, 0 ≤ c → c ≤ cN N → uSeq b N c = uSeq b (N - 1) (c + b c)) ∧
      (∀ c : ℝ, cN N ≤ c →
        0 ≤ v N c ∧ uSeq b N c = c - v N c + uSeq b (N - 1) (c + b (v N c))) ∧
      (∀ c : ℝ, 0 ≤ c → DifferentiableAt ℝ (uSeq b N) c → DifferentiableAt ℝ (uSeq b (N - 1)) c →
        deriv (uSeq b (N - 1)) c ≤ deriv (uSeq b N) c) := by sorry

end BellmanDP.Variational
