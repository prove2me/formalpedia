-- Prove2me | Theorems.Thm_Erdos81_root_problem
-- name    : Erdos81.root_problem
-- status  : Open
-- author  : @hao jia
-- created : 2026-09-08T05:06:16.994415+00:00
-- url     : https://prove2.me/theorems/6eccadbb-8a22-4567-a34c-58e6ddd9840f
-- title:
--   Erdos Problem 81: n²/6 plus a linear remainder
-- statement:
--   There are universal constants $C>0$ and $n_0\ge1$ such that every finite chordal graph $G$ on $n\ge n_0$ vertices has an exact edge partition into at most
--
--   $$
--   \frac{n^2}{6}+Cn
--   $$
--
--   complete subgraphs. The constants are chosen independently of $n$ and $G$, and the pieces partition edges rather than merely cover them.
-- source:
--   Erdos Problems, Problem 81, https://www.erdosproblems.com/81

import Definitions.Def_erdos81_clique_partitions

namespace Erdos81

/-- Erdős Problem 81: a universal linear remainder above `n²/6`. -/
theorem root_problem :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 1 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ G : SimpleGraph (Fin n),
        IsChordal G →
        HasCliquePartitionAtMost G ((n : ℝ) ^ 2 / 6 + C * n) := by sorry

end Erdos81
