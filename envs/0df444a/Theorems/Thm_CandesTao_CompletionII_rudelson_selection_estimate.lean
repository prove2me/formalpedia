-- Prove2me | Theorems.Thm_CandesTao_CompletionII_rudelson_selection_estimate
-- name    : CandesTao.CompletionII.rudelson_selection_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:53:54.204124+00:00
-- url     : https://prove2.me/theorems/d255e2ff-64fb-4ece-a7d4-d6c6eb35c0ec
-- title:
--   Theorem 3.2 — Rudelson selection estimate
-- statement:
--   Let $M \in \mathbb{R}^{n_1\times n_2}$ have a rank-$r$ SVD with column and row projections $P_U, P_V$, tangent-space projection $\mathcal{P}_T$, and suppose $M$ obeys (I.18) with parameter $\mu_0$:
--   $$\|P_U e_a\|^2 \le \frac{\mu_0 r}{n_1}, \qquad \|P_V e_b\|^2 \le \frac{\mu_0 r}{n_2} \qquad \text{for all } a \in [n_1],\ b \in [n_2].$$
--   Let $0 < m \le n_1n_2$, $p := m/(n_1n_2)$, and let $\Omega$ contain each entry independently with probability $p$ (the Bernoulli model). Put $n := \max(n_1, n_2)$.
--
--   There is an absolute constant $C_R > 0$ such that for every $\beta > 1$ the following holds. If
--   $$a := C_R\sqrt{\frac{\mu_0 nr(\beta\log n)}{m}} < 1,$$
--   then with probability at least $1 - 3n^{-\beta}$,
--   $$p^{-1}\|\mathcal{P}_T\mathcal{P}_\Omega\mathcal{P}_T - p\mathcal{P}_T\| \le a.$$
--   Here $\|\cdot\|$ is the operator norm on $\mathbb{R}^{n_1\times n_2}$ with the Frobenius norm.
--
--   The estimate is quoted by Candès and Tao from Candès and Recht (Theorem 4.1). It implies that $\mathcal{P}_\Omega$ is injective on $T$ and it controls the tail of the Neumann series for the dual certificate.
--
--   **Formalization Note** The operator norm is the platform's `tangentSamplingDeviation Ω S p`, the supremum of $p^{-1}\|\mathcal{P}_T\mathcal{P}_\Omega X - pX\|_F$ over $X \in T$ with $\|X\|_F \le 1$. This equals the operator norm because $\mathcal{P}_T\mathcal{P}_\Omega\mathcal{P}_T - p\mathcal{P}_T$ vanishes on $T^\perp$. The quantity $a$ is the platform's `tangentSamplingDeviationScale C_R β μ₀ n r m`. (I.18) is the platform's `A0 S μ₀`. The constant $C_R$ is quantified before $\beta$ and all the data, and the logarithm is natural. The statement is rectangular, as printed.
-- source:
--   Candès & Tao, The Power of Convex Relaxation: Near-Optimal Matrix Completion, IEEE Trans. Inf. Theory 56(5), 2010, p. 2060, Theorem 3.2 (Eqs. (III.6), (III.7)); (I.18) on p. 2057; quoted from Candès & Recht, Exact Matrix Completion via Convex Optimization, Theorem 4.1

import Definitions.Def_matrix_completion_tangent

open MatrixCompletion

namespace CandesTao.CompletionII

/-- Candès–Tao, Theorem 3.2 (Rudelson selection estimate), quoted from Candès–Recht,
Theorem 4.1.  There is an absolute constant `C_R > 0` such that for every `β > 1`,
every `n₁ × n₂` real matrix `M` with rank-`r` SVD `S` obeying (I.18) with parameter
`μ₀` (the platform's `A0`), and every `0 < m ≤ n₁ n₂`, with `n := max n₁ n₂`,
`p := m / (n₁ n₂)` and `a := C_R √(μ₀ n r (β log n) / m)` (III.7): if `a < 1`, then under
the Bernoulli model with parameter `p`,
`p⁻¹ ‖P_T P_Ω P_T - p P_T‖ ≤ a` (III.6) with probability at least `1 - 3 n^{-β}`.
The operator norm is `tangentSamplingDeviation`, the supremum over `X ∈ T`,
`‖X‖_F ≤ 1`, of `p⁻¹ ‖P_T P_Ω X - p X‖_F`. -/
theorem rudelson_selection_estimate :
    ∃ C_R : ℝ, 0 < C_R ∧
      ∀ β : ℝ, 1 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : RealMatrix n₁ n₂) (S : SVD M r) (μ₀ : ℝ),
        0 < m →
        m ≤ n₁ * n₂ →
        A0 S μ₀ →
        tangentSamplingDeviationScale C_R β μ₀ (max n₁ n₂) r m < 1 →
        1 - 3 * ((max n₁ n₂ : ℕ) : ℝ) ^ (-β) ≤
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Ω => tangentSamplingDeviation Ω S ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ≤
              tangentSamplingDeviationScale C_R β μ₀ (max n₁ n₂) r m) := by sorry

end CandesTao.CompletionII
