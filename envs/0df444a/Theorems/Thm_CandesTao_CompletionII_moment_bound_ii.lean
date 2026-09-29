-- Prove2me | Theorems.Thm_CandesTao_CompletionII_moment_bound_ii
-- name    : CandesTao.CompletionII.moment_bound_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:55:26.540407+00:00
-- url     : https://prove2.me/theorems/99d65e00-8bb8-49ae-81a3-422faf56c630
-- title:
--   Theorem 3.6 — Moment bound II (as derived in Section VI-B)
-- statement:
--   Let $M \in \mathbb{R}^{n\times n}$ be a fixed matrix with a rank-$r$ SVD obeying the strong incoherence property with parameter $\mu$, and put $r_\mu := \mu^2 r$ (III.25). Let $2nr \le m \le n^2$ (the standing assumption (I.22)) and $n r_\mu \le m$. Let $\Omega$ follow the Bernoulli model with $p = m/n^2$, and for $k \ge 0$ set
--   $$A = (\mathcal{Q}_\Omega\mathcal{Q}_T)^k\mathcal{Q}_\Omega(E).$$
--   There are absolute constants $C, c_0 > 0$ such that for every $k \ge 0$ and every $j \ge 1$ with $n \ge c_0 j(k+1)$,
--   $$\mathbb{E}\left[\operatorname{trace}\left((A^*A)^j\right)\right] \le n\left(\frac{C\,(j(k+1))^6\, n r_\mu}{m}\right)^{j(k+1)}.$$
--
--   By Markov's inequality this bounds the spectral norm of $A$ with high probability. Together with Lemma 3.3 and Theorem 3.2 it gives Corollary 3.7, and the linear dependence on $r$ is what makes Theorem 1.2 nearly optimal.
--
--   **Formalization Note** This is a **correction** of the printed (III.27), which reads $\mathbb{E}[\operatorname{trace}(A^*A)^j] \le ((j(k+1))^6 n r_\mu/m)^{j(k+1)}$. As printed the bound is false. For $k = 0$ and $j = 1$, $\mathbb{E}\operatorname{trace}(A^*A) = r(1-p)/p$ exactly. For a flat rank-one matrix ($\mu = 1$) this exceeds the printed right-hand side $r/(np)$ by the factor $n(1-p)$. The statement here is the bound the paper actually derives at the end of Section VI-B (p. 2070), $X \le O(j(k+1))^{6j(k+1)}(r_\mu/np)^{j(k+1)}n$, with $r_\mu/(np) = n r_\mu/m$ and the $O(\cdot)$ constant raised to the sixth power absorbed into $C$.
--
--   The hypothesis $n r_\mu \le m$ (that is, $r_\mu \le np$) is used in that derivation's step $(r_\mu/np)^{2j(k+1)-|\Omega|} \le (r_\mu/np)^{j(k+1)}$. It follows from (I.12), which is among "the assumptions of Theorem 1.2", as soon as $C\log^6 n \ge 1$. $C$ and $c_0$ are quantified before all data. Matrices are real, so $A^* = A^T$.
-- source:
--   Candès & Tao, The Power of Convex Relaxation: Near-Optimal Matrix Completion, IEEE Trans. Inf. Theory 56(5), 2010, p. 2063, Theorem 3.6, Eq. (III.27); corrected form from Section VI-B, p. 2070 (final display); r_μ from (III.25)

import Definitions.Def_matrix_completion_bernoulli
import Definitions.Def_CandesTao_Shared_StrongIncoherence
import Definitions.Def_CandesTao_CompletionII_CenteredOperators

open MatrixCompletion

namespace CandesTao.CompletionII

/-- Candès–Tao, Theorem 3.6 (Moment Bound II), square case, in the form derived at the
end of Section VI-B (p. 2070); the printed (III.27) omits the factor `n` and the
`O(1)^{j(k+1)}` constant and is false as printed (see the natural-language statement).
There are absolute constants `C, c₀ > 0` such that the following holds.  Let `M` be a fixed
`n × n` matrix with rank-`r` SVD `S` obeying strong incoherence with parameter `μ`, let
`r_μ := μ² r`, let `2nr ≤ m ≤ n²` (standing assumption (I.22)) and `n r_μ ≤ m`, and let `Ω`
follow the Bernoulli model with `p = m/n²`.  For `k ≥ 0` put `A := (Q_Ω Q_T)^k Q_Ω(E)`.
Then for every `j ≥ 1` with `n ≥ c₀ j (k+1)`,
`𝔼 trace((A*A)^j) ≤ n · (C (j(k+1))⁶ n r_μ / m)^{j(k+1)}`. -/
theorem moment_bound_ii :
    ∃ C : ℝ, 0 < C ∧ ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (n r m : ℕ) (M : RealMatrix n n) (S : SVD M r) (μ : ℝ) (k j : ℕ),
        CandesTao.Shared.StrongIncoherence S μ →
        2 * n * r ≤ m →
        m ≤ n * n →
        (n : ℝ) * (μ ^ 2 * (r : ℝ)) ≤ (m : ℝ) →
        c₀ * ((j : ℝ) * ((k : ℝ) + 1)) ≤ (n : ℝ) →
        1 ≤ j →
        bernoulliExpectation ((m : ℝ) / (n : ℝ) ^ 2)
            (fun Ω => Matrix.trace
              ((Matrix.transpose (momentMatrix S Ω ((m : ℝ) / (n : ℝ) ^ 2) k) *
                  momentMatrix S Ω ((m : ℝ) / (n : ℝ) ^ 2) k) ^ j)) ≤
          (n : ℝ) *
            (C * ((j : ℝ) * ((k : ℝ) + 1)) ^ 6 * (n : ℝ) * (μ ^ 2 * (r : ℝ)) / (m : ℝ)) ^
              (j * (k + 1)) := by sorry

end CandesTao.CompletionII
