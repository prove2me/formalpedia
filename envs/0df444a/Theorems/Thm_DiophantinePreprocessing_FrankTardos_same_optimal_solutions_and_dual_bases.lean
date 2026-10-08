-- Prove2me | Theorems.Thm_DiophantinePreprocessing_FrankTardos_same_optimal_solutions_and_dual_bases
-- name    : DiophantinePreprocessing.FrankTardos.same_optimal_solutions_and_dual_bases
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:43:56.686293+00:00
-- url     : https://prove2.me/theorems/1fa0af47-d4ca-4584-9d9e-0d1429dbe8cd
-- title:
--   Theorem 4.2 — a small integral objective with the same optimal solutions and optimal dual bases
-- statement:
--   Let $n \ge 0$, let $w \in \mathbb{Q}^n$ be a rational objective and put $N = (n+1)! + 1$. There is an integral vector $\tilde w \in \mathbb{Z}^n$ with
--   $$\|\tilde w\|_\infty \le 2^{4n^3} N^{n(n+2)}, \qquad N = (n+1)! + 1,$$
--   such that for every $m$, every $m \times n$ matrix $A$ with entries in $\{0, +1, -1\}$ and every $b \in \mathbb{R}^m$, with $P = \{x \in \mathbb{R}^n : Ax \le b\}$:
--
--   1. a point $x \in P$ is $w$-maximal if and only if it is $\tilde w$-maximal;
--   2. a set of rows of $A$ is an optimal dual basis for $\max\{wx : Ax \le b\}$ if and only if it is an optimal dual basis for $\max\{\tilde w x : Ax \le b\}$.
--
--   In the paper $\tilde w$ is the output of the preprocessing algorithm applied to $w$ and $N$. The theorem lets any linear-programming algorithm whose running time is polynomial in $n$ and in the length of the objective be run on $\tilde w$ instead of $w$, whose length is polynomial in $n$ alone, which is how polynomial algorithms over $0, \pm1$ polyhedra become strongly polynomial.
--
--   **Formalization Note** "The output of the preprocessing algorithm" is replaced by the guarantee it provides: the statement asserts the existence of an integral $\tilde w$ with the explicit size bound of the Output line (p. 55). $\tilde w$ is chosen before $A$ and $b$, so one vector works for every $0, \pm 1$ matrix with $n$ columns and every right-hand side. The size bound is essential: without it a multiple of $w$ by a common denominator would satisfy the conclusion.
-- source:
--   Frank & Tardos, An application of simultaneous diophantine approximation in combinatorial optimization, Combinatorica 7(1) (1987), p. 58, Theorem 4.2 (with the preceding sentence defining w̃ and N = (n+1)! + 1); Output line p. 55; standing assumption of Sect. 4, p. 56

import Mathlib
import Definitions.Def_DiophantinePreprocessing_FrankTardos_IsWMaximal
import Definitions.Def_DiophantinePreprocessing_FrankTardos_IsOptimalDualBasis

namespace DiophantinePreprocessing.FrankTardos

/-- Frank–Tardos, Theorem 4.2 (p. 58), existence form: for every rational `w ∈ ℚⁿ` there is an
integral `w̃` with `‖w̃‖∞ ≤ 2^{4n³} N^{n(n+2)}`, `N = (n+1)! + 1` (the output of the
preprocessing algorithm applied to `w` and `N`), such that for every matrix `A` with entries
`0, ±1` and every `b`: (i) `x ∈ P = {x : A x ≤ b}` is `w`-maximal iff it is `w̃`-maximal, and
(ii) a set of rows of `A` is an optimal dual basis for `max (w x : A x ≤ b)` iff it is one for
`max (w̃ x : A x ≤ b)`. -/
theorem same_optimal_solutions_and_dual_bases (n : ℕ) (w : Fin n → ℚ) :
    ∃ wt : Fin n → ℤ,
      (∀ j, |wt j| ≤ 2 ^ (4 * n ^ 3) * (((n + 1).factorial : ℤ) + 1) ^ (n * (n + 2))) ∧
      ∀ (m : ℕ) (A : Matrix (Fin m) (Fin n) ℤ),
        (∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) →
        ∀ b : Fin m → ℝ,
          (∀ x : Fin n → ℝ,
            IsWMaximal A b (fun j => (w j : ℝ)) x ↔ IsWMaximal A b (fun j => (wt j : ℝ)) x) ∧
          (∀ B : Finset (Fin m),
            IsOptimalDualBasis A b (fun j => (w j : ℝ)) B ↔
              IsOptimalDualBasis A b (fun j => (wt j : ℝ)) B) := by sorry

end DiophantinePreprocessing.FrankTardos
