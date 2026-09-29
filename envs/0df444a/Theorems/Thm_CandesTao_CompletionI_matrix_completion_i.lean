-- Prove2me | Theorems.Thm_CandesTao_CompletionI_matrix_completion_i
-- name    : CandesTao.CompletionI.matrix_completion_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:43:08.940988+00:00
-- url     : https://prove2.me/theorems/c817d9d5-85a1-4670-9cb4-eae5441aea47
-- title:
--   Theorem 1.1 (Matrix Completion I), general-rank form (I.11): $m \ge C\mu^4 n r^2(\log n)^2$ samples suffice
-- statement:
--   There is an absolute constant $C > 0$ such that the following holds. Let $M \in \mathbb R^{n\times n}$ be a fixed matrix of rank $r$ that obeys the strong incoherence property with parameter $\mu$. Suppose that $m \le n^2$ entries of $M$ are observed, their locations $\Omega$ being chosen uniformly at random among all subsets of $[n]\times[n]$ of cardinality $m$. If
--   $$m \ge C\mu^4 n r^2 (\log n)^2,$$
--   then with probability at least $1 - n^{-3}$, $M$ is the unique solution of the nuclear-norm minimization program
--   $$\text{minimize } \|X\|_* \quad\text{subject to}\quad X_{ab} = M_{ab} \text{ for all } (a,b) \in \Omega. \qquad \text{(I.3)}$$
--
--   For bounded rank $r = O(1)$ this is Theorem 1.1 of Candès and Tao: nuclear-norm minimization recovers every strongly incoherent low-rank matrix from $O(n(\log n)^2)$ random entries, which is within a logarithmic factor of the information-theoretic limit $n\log n$.
--
--   **Formalization Note** The paper prints Theorem 1.1 for $r = O(1)$ with condition (I.10), $m \ge C\mu^4 n(\log n)^2$, and states on the same page that the proof gives exact recovery for every $r$ under (I.11), $m \ge C\mu^4 n r^2(\log n)^2$; this general-rank form is formalized. The constant $C$ is quantified before $n$, $r$, $m$, $M$ and $\mu$. Only the square case $n_1 = n_2 = n$ is stated, which is the case the paper proves (Section I-H). The paper's standing assumptions $n \ge C'$ and $m \ge 2nr$ are not hypotheses: they are absorbed by the choice of $C$ (strong incoherence forces $\mu \ge 1$ when $r \ge 1$). The hypothesis $m \le n^2$ keeps the uniform model nonempty. $\log$ is the natural logarithm, and the probability is the platform's `successProb`, the fraction of $m$-subsets on which $M$ is the unique minimizer; the SVD is any rank-$r$ SVD of $M$ (strong incoherence does not depend on the choice).
-- source:
--   Candès & Tao, The Power of Convex Relaxation: Near-Optimal Matrix Completion, IEEE Trans. Inf. Theory 56(5), 2010, p. 2055, Theorem 1.1 and Eq. (I.11)

import Definitions.Def_matrix_completion_basic
import Definitions.Def_CandesTao_Shared_StrongIncoherence

open MatrixCompletion

namespace CandesTao.CompletionI

/-- Candès–Tao, Theorem 1.1 (Matrix Completion I) in the general-rank form (I.11),
square case `n₁ = n₂ = n`: there is an absolute constant `C > 0` such that for every
fixed `n × n` real matrix `M` with a rank-`r` SVD `S` obeying the strong incoherence
property with parameter `μ`, if `m` entries are observed uniformly at random
(`m ≤ n²`) and `m ≥ C μ⁴ n r² (log n)²`, then `M` is the unique solution of the
nuclear-norm program (I.3) with probability at least `1 - n⁻³`. -/
theorem matrix_completion_i :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n r m : ℕ) (M : RealMatrix n n) (S : SVD M r) (μ : ℝ),
        CandesTao.Shared.StrongIncoherence S μ →
        m ≤ n * n →
        C * μ ^ 4 * (n : ℝ) * (r : ℝ) ^ 2 * (Real.log (n : ℝ)) ^ 2 ≤ (m : ℝ) →
        1 - 1 / (n : ℝ) ^ 3 ≤ successProb m M := by sorry

end CandesTao.CompletionI
