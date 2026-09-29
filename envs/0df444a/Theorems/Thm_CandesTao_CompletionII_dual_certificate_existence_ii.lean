-- Prove2me | Theorems.Thm_CandesTao_CompletionII_dual_certificate_existence_ii
-- name    : CandesTao.CompletionII.dual_certificate_existence_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:55:50.880961+00:00
-- url     : https://prove2.me/theorems/95970d70-d122-4ab2-9121-2fe337cc48ca
-- title:
--   Corollary 3.7 — Existence of dual certificate II
-- statement:
--   Let $M \in \mathbb{R}^{n\times n}$ be a fixed matrix with a rank-$r$ SVD obeying the strong incoherence property with parameter $\mu$, with sign matrix $E$, tangent space $T$ and projections $\mathcal{P}_T$, $\mathcal{P}_{T^\perp}$. Let $\Omega$ follow the Bernoulli model with $p = m/n^2$, $m \le n^2$.
--
--   There is an absolute constant $C > 0$ such that if
--   $$m \ge C\mu^2 nr\log^6 n \qquad \text{(I.12)},$$
--   then with probability at least $1 - n^{-3}$ the following both hold:
--
--   1. $\mathcal{P}_\Omega$ restricted to $T$ is injective;
--   2. the matrix $Y$ of (III.10), the minimum-Frobenius-norm matrix with $\mathcal{P}_\Omega(Y) = Y$ and $\mathcal{P}_T(Y) = E$, obeys
--   $$\|\mathcal{P}_{T^\perp}(Y)\| \le 1/2.$$
--
--   In particular $Y$ is a dual certificate in the sense of Lemma 3.1. Combined with Lemma 3.1 this gives Theorem 1.2 under the Bernoulli model.
--
--   **Formalization Note** $Y$ of (III.10), $Y = \mathcal{P}_\Omega\mathcal{P}_T(\mathcal{P}_T\mathcal{P}_\Omega\mathcal{P}_T)^{-1}E$, is defined only when $\mathcal{P}_\Omega$ is injective on $T$. It is characterized by the platform's `LeastSquaresDualCertificate`, the minimum-norm solution of $\mathcal{P}_\Omega(Y) = Y$, $\mathcal{P}_T(Y) = E$, as the paper notes on p. 2061. Injectivity is therefore part of the event. $\|\cdot\|$ is the spectral norm, $\log$ is natural, and $C$ is quantified before all data. The paper's standing assumptions $n \ge C'$ and $m \ge 2nr$ are absorbed by $C$.
-- source:
--   Candès & Tao, The Power of Convex Relaxation: Near-Optimal Matrix Completion, IEEE Trans. Inf. Theory 56(5), 2010, p. 2063, Corollary 3.7; (III.10) and its least-squares characterization on p. 2061; (I.12) on p. 2055

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_CandesTao_Shared_StrongIncoherence

open MatrixCompletion

namespace CandesTao.CompletionII

/-- Candès–Tao, Corollary 3.7 (Existence of Dual Certificate II), square case.  There is
an absolute constant `C > 0` such that for every fixed `n × n` matrix `M` with rank-`r` SVD
`S` obeying strong incoherence with parameter `μ`, if `m ≤ n²` and
`m ≥ C μ² n r (log n)⁶` (I.12), then under the Bernoulli model with `p = m/n²`, with
probability at least `1 - n⁻³` the restriction of `P_Ω` to `T` is injective and the
certificate `Y` of (III.10) (the minimum-Frobenius-norm `Y` with `P_Ω(Y) = Y` and
`P_T(Y) = E`) obeys `‖P_{T⊥}(Y)‖ ≤ 1/2`; in particular `Y` is a dual certificate in the
sense of Lemma 3.1. -/
theorem dual_certificate_existence_ii :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n r m : ℕ) (M : RealMatrix n n) (S : SVD M r) (μ : ℝ),
        CandesTao.Shared.StrongIncoherence S μ →
        m ≤ n * n →
        C * μ ^ 2 * (n : ℝ) * (r : ℝ) * (Real.log (n : ℝ)) ^ 6 ≤ (m : ℝ) →
        1 - 1 / (n : ℝ) ^ 3 ≤
          bernoulliEventProb ((m : ℝ) / (n : ℝ) ^ 2)
            (fun Ω => SamplingOperatorInjectiveOnT Ω S ∧
              ∃ Y : RealMatrix n n, LeastSquaresDualCertificate Ω S Y ∧
                spectralNorm (normalProjection S Y) ≤ 1 / 2) := by sorry

end CandesTao.CompletionII
