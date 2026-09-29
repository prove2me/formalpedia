-- Prove2me | Theorems.Thm_CandesTao_CompletionI_moment_bound_i
-- name    : CandesTao.CompletionI.moment_bound_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:42:21.113889+00:00
-- url     : https://prove2.me/theorems/6bc6b715-ec94-424c-8e5e-408d97071587
-- title:
--   Theorem 3.4 — Moment bound I: $\mathbb E\operatorname{trace}(A^*A)^j = O(j(k+1))^{2j(k+1)}\, n\,(nr_\mu^2/m)^{j(k+1)}$
-- statement:
--   There are absolute constants $C, c_0 > 0$ such that the following holds. Let $M$ be a fixed real $n\times n$ matrix with a rank-$r$ SVD obeying the strong incoherence property with parameter $\mu$, and put $r_\mu := \mu^2 r$. Let $m$ satisfy $2nr \le m \le n^2$, and let $\Omega$ be drawn from the Bernoulli model in which each entry is observed independently with probability $p = m/n^2$. For $k \ge 0$ let
--   $$A = (\mathcal Q_\Omega \mathcal Q_T)^k \mathcal Q_\Omega(E),$$
--   with $\mathcal Q_\Omega = p^{-1}\mathcal P_\Omega - \mathcal I$ and $\mathcal Q_T = \mathcal P_T - \rho'\mathcal I$. Then for every integer $j \ge 1$, if $m \ge n r_\mu^2$ and $n \ge c_0\, j(k+1)$,
--   $$\mathbb E\bigl[\operatorname{trace}(A^*A)^j\bigr] \le \bigl(C j(k+1)\bigr)^{2j(k+1)}\; n\left(\frac{n r_\mu^2}{m}\right)^{j(k+1)} .$$
--
--   Since $\|A\|^{2j} \le \operatorname{trace}(A^*A)^j$, Markov's inequality turns this moment bound into a tail bound on $\|(\mathcal Q_\Omega\mathcal Q_T)^k\mathcal Q_\Omega(E)\|$ for each $k \le \log n$, which is how the dual certificate of Corollary 3.5 is controlled.
--
--   **Formalization Note** The paper writes the bound as $O(j(k+1))^{2j(k+1)}\,n\,(nr_\mu^2/m)^{j(k+1)}$ with $O(M)^M := (CM)^M$ (Section I-H); the expectation is nonnegative, so the bound is stated as an upper bound, with $C$ and $c_0$ quantified before every other variable. The hypothesis $2nr \le m$ is the paper's standing assumption (I.22), and "the assumptions of Theorem 1.1" are read as: $M$ fixed, strongly incoherent with parameter $\mu$, $\Omega$ Bernoulli with $p = m/n^2$; the theorem's own provisos $m \ge nr_\mu^2$ and $n \ge c_0 j(k+1)$ replace the sampling condition (I.10), and the bounded-rank assumption is not used (the bound is explicit in $r$). Only the square case is stated, as in the paper. $A^*$ is the transpose (real matrices).
-- source:
--   Candès & Tao, The Power of Convex Relaxation: Near-Optimal Matrix Completion, IEEE Trans. Inf. Theory 56(5), 2010, p. 2063, Theorem 3.4, Eq. (III.25); standing assumption (I.22), p. 2059

import Definitions.Def_matrix_completion_bernoulli
import Definitions.Def_CandesTao_Shared_StrongIncoherence
import Definitions.Def_CandesTao_CompletionI_MomentMatrix

open MatrixCompletion

namespace CandesTao.CompletionI

/-- Candès–Tao, Theorem 3.4 (Moment Bound I), square case.  There are absolute constants
`C, c₀ > 0` such that the following holds.  Let `M` be a fixed `n × n` matrix with rank-`r`
SVD `S` obeying strong incoherence with parameter `μ`, let `r_μ := μ² r`, let
`2nr ≤ m ≤ n²` (standing assumption (I.22)), and let `Ω` follow the Bernoulli model with
`p = m/n²`.  For `k ≥ 0` put `A := (Q_Ω Q_T)^k Q_Ω(E)`.  Then for every `j ≥ 1`, if
`m ≥ n r_μ²` and `n ≥ c₀ j (k+1)`,
`𝔼 trace((A*A)^j) ≤ (C j (k+1))^(2j(k+1)) · n · (n r_μ² / m)^(j(k+1))`. -/
theorem moment_bound_i :
    ∃ C : ℝ, 0 < C ∧ ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (n r m : ℕ) (M : RealMatrix n n) (S : SVD M r) (μ : ℝ) (k j : ℕ),
        CandesTao.Shared.StrongIncoherence S μ →
        2 * n * r ≤ m →
        m ≤ n * n →
        (n : ℝ) * (μ ^ 2 * (r : ℝ)) ^ 2 ≤ (m : ℝ) →
        c₀ * ((j : ℝ) * ((k : ℝ) + 1)) ≤ (n : ℝ) →
        1 ≤ j →
        bernoulliExpectation ((m : ℝ) / (n : ℝ) ^ 2)
            (fun Ω => Matrix.trace
              ((Matrix.transpose (momentMatrix S Ω ((m : ℝ) / (n : ℝ) ^ 2) k) *
                  momentMatrix S Ω ((m : ℝ) / (n : ℝ) ^ 2) k) ^ j)) ≤
          (C * ((j : ℝ) * ((k : ℝ) + 1))) ^ (2 * j * (k + 1)) * (n : ℝ) *
            ((n : ℝ) * (μ ^ 2 * (r : ℝ)) ^ 2 / (m : ℝ)) ^ (j * (k + 1)) := by sorry

end CandesTao.CompletionI
