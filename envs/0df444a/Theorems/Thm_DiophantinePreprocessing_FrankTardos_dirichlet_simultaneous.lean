-- Prove2me | Theorems.Thm_DiophantinePreprocessing_FrankTardos_dirichlet_simultaneous
-- name    : DiophantinePreprocessing.FrankTardos.dirichlet_simultaneous
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:40:21.851178+00:00
-- url     : https://prove2.me/theorems/254b7110-dc41-434e-a67e-59d6f522a6a3
-- title:
--   Sect. 2 — Dirichlet's simultaneous approximation theorem [2, Sect. 1.10]
-- statement:
--   Let $N$ be a positive integer and $\alpha(1), \dots, \alpha(n)$ real numbers. Then there are integers $p(1), \dots, p(n)$ and $q$ such that $1 \le q \le N^n$ and
--   $$|q\,\alpha(i) - p(i)| < \frac{1}{N} \qquad (i = 1, \dots, n).$$
--
--   This is Dirichlet's theorem on simultaneous Diophantine approximation: one common denominator $q$ of size at most $N^n$ approximates all $n$ numbers to within $1/N$. It is the existence statement behind the decomposition of Theorem 3.1.
--
--   **Formalization Note** The inequality is strict and the bound on $q$ is $N^n$, both as on the page. For $n = 0$ the statement holds with $q = 1$.
-- source:
--   Frank & Tardos, An application of simultaneous diophantine approximation in combinatorial optimization, Combinatorica 7(1) (1987), p. 52, Sect. 2, Dirichlet's theorem [2, Sect. 1.10] (Cassels, An Introduction to Diophantine Approximation)

import Mathlib

namespace DiophantinePreprocessing.FrankTardos

/-- Dirichlet's simultaneous approximation theorem (Frank–Tardos, Sect. 2, p. 52, citing
Cassels, Sect. 1.10). -/
theorem dirichlet_simultaneous (n N : ℕ) (hN : 0 < N) (α : Fin n → ℝ) :
    ∃ (p : Fin n → ℤ) (q : ℤ), 1 ≤ q ∧ q ≤ (N : ℤ) ^ n ∧
      ∀ i, |(q : ℝ) * α i - (p i : ℝ)| < 1 / (N : ℝ) := by sorry

end DiophantinePreprocessing.FrankTardos
