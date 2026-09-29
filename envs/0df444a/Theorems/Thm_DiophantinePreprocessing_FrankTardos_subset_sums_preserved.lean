-- Prove2me | Theorems.Thm_DiophantinePreprocessing_FrankTardos_subset_sums_preserved
-- name    : DiophantinePreprocessing.FrankTardos.subset_sums_preserved
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:42:15.600496+00:00
-- url     : https://prove2.me/theorems/b4c38719-74d7-41fe-bcdd-46f1bd4d47b9
-- title:
--   Sect. 3 (p. 55) — a small integral $\tilde w$ with the same order on subset sums
-- statement:
--   For a vector $w \in \mathbb{Q}^n$ and a subset $X \subseteq \{1, \dots, n\}$ write $w(X) = \sum_{i \in X} w(i)$. For every rational $w \in \mathbb{Q}^n$ there is an integral vector $\tilde w \in \mathbb{Z}^n$ with
--   $$\|\tilde w\|_\infty \le 2^{4n^3} (n+1)^{n(n+2)}$$
--   such that for all subsets $X, Y$ of the coordinates
--   $$\tilde w(X) \le \tilde w(Y) \iff w(X) \le w(Y).$$
--
--   This is the special case $N = n + 1$ of the preprocessing algorithm: every comparison of two subset sums is decided identically by $w$ and by an integral $\tilde w$ whose entries have $O(n^3)$ bits.
--
--   **Formalization Note** The page states the size as "$\log\|\tilde w\|_\infty$ is $O(n^3)$"; the statement uses the explicit bound $2^{4n^3}N^{n(n+2)}$ of the Output line (p. 55) with $N = n + 1$, which is what the paper's algorithm delivers.
-- source:
--   Frank & Tardos, An application of simultaneous diophantine approximation in combinatorial optimization, Combinatorica 7(1) (1987), p. 55, paragraph before the Preprocessing algorithm (case N = n + 1)

import Mathlib

namespace DiophantinePreprocessing.FrankTardos

/-- Frank–Tardos, p. 55 (the case `N = n + 1` of the preprocessing algorithm): every rational
`w ∈ ℚⁿ` has an integral `w̃` with `‖w̃‖∞ ≤ 2^{4n³} (n+1)^{n(n+2)}` such that
`w̃(X) ≤ w̃(Y) ↔ w(X) ≤ w(Y)` for all subsets `X, Y` of the coordinates. -/
theorem subset_sums_preserved (n : ℕ) (w : Fin n → ℚ) :
    ∃ wt : Fin n → ℤ,
      (∀ j, |wt j| ≤ 2 ^ (4 * n ^ 3) * ((n : ℤ) + 1) ^ (n * (n + 2))) ∧
      ∀ X Y : Finset (Fin n),
        (∑ j ∈ X, wt j ≤ ∑ j ∈ Y, wt j ↔ ∑ j ∈ X, w j ≤ ∑ j ∈ Y, w j) := by sorry

end DiophantinePreprocessing.FrankTardos
