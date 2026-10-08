-- Prove2me | Theorems.Thm_BellmanDP_Fibonacci_discrete_search_corrected
-- name    : BellmanDP.Fibonacci.discrete_search_corrected
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T14:44:22.189356+00:00
-- url     : https://prove2.me/theorems/fb547710-1e8c-48f0-9b3b-270df0d9741f
-- title:
--   Chapter I, Theorem 12 (corrected) — $K_0=K_1=1$, $K_2=2$, $K_3=4$, $K_n = F_{n+1}-1$ for $n\ge 3$
-- statement:
--   For $n \ge 0$ let $K_n$ be the largest number $N \ge 1$ of points $0, 1, \dots, N-1$ such that some deterministic adaptive procedure, for every function $f$ strictly unimodal on these points, evaluates $f$ at most $n$ times and then names the point at which $f$ is maximal. Then $K_n$ exists for every $n$, and
--   $$K_0 = 1,\quad K_1 = 1,\quad K_2 = 2,\quad K_3 = 4,\qquad K_n = F_{n+1} - 1 \quad (n \ge 3),$$
--   where $F_0 = F_1 = 1$, $F_k = F_{k-1} + F_{k-2}$.
--
--   **Correction.** Bellman prints (7) as $K_n = 1 + F_n$ for $n \ge 3$. This agrees with the corrected formula at $n = 3$ but is false from $n = 4$ on: on seven points, evaluate the third and the fifth; if $f(3) > f(5)$ the maximum is among the first four points and $f(3)$ is known, so evaluating the second point and then the first or the fourth identifies it; the case $f(5) > f(3)$ is symmetric, and $f(3) = f(5)$ forces the maximum at the fourth point. Hence $K_4 \ge 7 > 6 = 1 + F_4$. The printed initial values $K_0, \dots, K_3$ are kept.
--
--   **Formalization Note** Each value is stated as `IsGreatest` of the set of searchable point counts, which asserts both that the maximum exists and what it is.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter I, § 22, Theorem 12 (Eq. (22.7), corrected), p. 36

import Mathlib
import Definitions.Def_BellmanDP_Fibonacci_SearchModel

namespace BellmanDP.Fibonacci

/-- Bellman, Ch. I, § 22, Theorem 12, p. 36, **corrected**. The book prints `K₀ = 1, K₁ = 1,
K₂ = 2, K₃ = 4` and `K_n = 1 + F_n` for `n ≥ 3`; the latter is false from `n = 4` on (seven
points can be searched with four evaluations, while `1 + F₄ = 6`). The corrected statement keeps
the printed initial values and replaces (7) by `K_n = F_{n+1} − 1` for `n ≥ 3` (which agrees with
the printed value at `n = 3`). Here `K_n` is the greatest number of points on which the maximum
of every strictly unimodal function can always be identified in `n` computations. -/
theorem discrete_search_corrected :
    IsGreatest (identifiableSizes 0) 1 ∧
    IsGreatest (identifiableSizes 1) 1 ∧
    IsGreatest (identifiableSizes 2) 2 ∧
    IsGreatest (identifiableSizes 3) 4 ∧
    ∀ n : ℕ, 3 ≤ n → IsGreatest (identifiableSizes n) (bookFib (n + 1) - 1) := by sorry

end BellmanDP.Fibonacci
