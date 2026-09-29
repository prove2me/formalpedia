-- Prove2me | Theorems.Thm_CandesTao_CompletionII_matrix_completion_ii
-- name    : CandesTao.CompletionII.matrix_completion_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:56:11.457405+00:00
-- url     : https://prove2.me/theorems/fc5b8bdf-e879-4c81-8677-4827fbe36113
-- title:
--   Theorem 1.2 — Matrix Completion II
-- statement:
--   Let $M \in \mathbb{R}^{n\times n}$ be a fixed matrix with a rank-$r$ singular value decomposition that obeys the strong incoherence property with parameter $\mu$. Suppose we observe $m \le n^2$ entries of $M$, at locations $\Omega$ sampled uniformly at random among all sets of $m$ entries, and consider the nuclear-norm program
--   $$\text{minimize } \|X\|_* \quad \text{subject to } X_{ij} = M_{ij} \text{ for all } (i,j) \in \Omega. \qquad \text{(I.3)}$$
--   There is an absolute constant $C > 0$ such that if
--   $$m \ge C\mu^2 nr\log^6 n, \qquad \text{(I.12)}$$
--   then $M$ is the unique solution of (I.3) with probability at least $1 - n^{-3}$.
--
--   The result is nearly optimal. By Theorem 1.7 of the same paper, no method can recover such matrices from fewer than a constant times $\mu_0 nr\log n$ entries, so the number of entries convex relaxation needs is at most a polylogarithmic factor above the information-theoretic limit.
--
--   **Formalization Note** This formalizes the square case $n_1 = n_2 = n$, which is the case the paper proves (Section I-H). "Under the same hypotheses as in Theorem 1.1" is read as the matrix hypotheses (a fixed matrix, strong incoherence, uniform sampling). It is not read as $r = O(1)$: the statement holds for every rank $r$, and (I.12) carries the dependence on $r$. The probability is the platform's `successProb m M`, the fraction of $m$-subsets on which $M$ is the unique minimizer. The hypothesis $m \le n^2$ is required because that probability is $0$ for $m > n^2$. $C$ is quantified before all data and absorbs the standing assumptions $n \ge C'$ and $m \ge 2nr$ of Section I-H. $\log$ is natural.
-- source:
--   Candès & Tao, The Power of Convex Relaxation: Near-Optimal Matrix Completion, IEEE Trans. Inf. Theory 56(5), 2010, p. 2055, Theorem 1.2 (Eq. (I.12)) with the hypotheses of Theorem 1.1

import Definitions.Def_matrix_completion_basic
import Definitions.Def_CandesTao_Shared_StrongIncoherence

open MatrixCompletion

namespace CandesTao.CompletionII

/-- Candès–Tao, Theorem 1.2 (Matrix Completion II), square case `n₁ = n₂ = n`, every
rank `r`: there is an absolute constant `C > 0` such that for every fixed `n × n` real
matrix `M` with a rank-`r` SVD `S` obeying the strong incoherence property with parameter
`μ`, if `m` entries are observed at locations sampled uniformly at random (`m ≤ n²`) and
`m ≥ C μ² n r (log n)⁶` (I.12), then `M` is the unique solution of the nuclear-norm
program (I.3) with probability at least `1 - n⁻³`. -/
theorem matrix_completion_ii :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n r m : ℕ) (M : RealMatrix n n) (S : SVD M r) (μ : ℝ),
        CandesTao.Shared.StrongIncoherence S μ →
        m ≤ n * n →
        C * μ ^ 2 * (n : ℝ) * (r : ℝ) * (Real.log (n : ℝ)) ^ 6 ≤ (m : ℝ) →
        1 - 1 / (n : ℝ) ^ 3 ≤ successProb m M := by sorry

end CandesTao.CompletionII
