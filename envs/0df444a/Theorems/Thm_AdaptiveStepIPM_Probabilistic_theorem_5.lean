-- Prove2me | Theorems.Thm_AdaptiveStepIPM_Probabilistic_theorem_5
-- name    : AdaptiveStepIPM.Probabilistic.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:21:25.996763+00:00
-- url     : https://prove2.me/theorems/6279eb75-3c49-4301-bb2b-881069f2e1d3
-- title:
--   Theorem 5 — negative projection product for a random subspace
-- statement:
--   For each $n$, fix any vector $r_n\in\mathbb R^n$ and any integer $d_n\le n$. Draw a uniformly random $d_n$-dimensional subspace $U_n$, and let $p_n$ and $q_n$ be the orthogonal projections of $r_n$ onto $U_n$ and $U_n^\perp$. Write $P_n=\operatorname{diag}(p_n)$. Then
--
--   $$
--   \Pr\!\left(\|P_nq_n\|^-_\infty
--     \le\frac{\log n}{n}\|r_n\|_2^2\right)
--     \longrightarrow1\quad\text{as }n\longrightarrow\infty.
--   $$
--
--   This controls the negative part of the second-order term in the paper's primal–dual search direction. It is a statement about each random subspace separately and does not assert independence across algorithm iterations.
--
--   **Formalization Note** $U_n$ is the null space of an $(n-d_n)\times n$ matrix with independent standard normal entries, as in the paper's example; it has the invariant $d_n$-subspace law almost surely. The probability is converted to a real number before taking the limit. The vector $r_n$ may vanish, and no normalization is imposed on it.
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), p. 13, Theorem 5; https://doi.org/10.1287/moor.18.4.964

import Definitions.Def_AdaptiveStepIPM_Probabilistic_Model

open MeasureTheory ProbabilityTheory Filter

namespace AdaptiveStepIPM.Probabilistic

/-- Theorem 5: the random-subspace second-order term has a small negative part. -/
theorem theorem_5 (d : ℕ → ℕ) (hd : ∀ n, d n ≤ n)
    (r : (n : ℕ) → EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun n : ℕ =>
      ((gaussianMatrix (n - d n) n)
        {G | negSupNorm (pq (n - d n) n G (r n)) ≤
          Real.log (n : ℝ) / (n : ℝ) * ‖r n‖ ^ 2}).toReal)
      atTop (nhds 1) := by sorry

end AdaptiveStepIPM.Probabilistic
