-- Prove2me | Theorems.Thm_CandesTao_CompletionI_dual_certificate_existence_i
-- name    : CandesTao.CompletionI.dual_certificate_existence_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:42:51.238161+00:00
-- url     : https://prove2.me/theorems/d5e8ac4b-bf8b-429c-8749-927cbae9e6d0
-- title:
--   Corollary 3.5 — Existence of dual certificate I, general-rank form
-- statement:
--   There is an absolute constant $C > 0$ such that the following holds. Let $M$ be a fixed real $n\times n$ matrix with a rank-$r$ SVD obeying the strong incoherence property with parameter $\mu$, let $m \le n^2$ satisfy
--   $$m \ge C\mu^4 n r^2 (\log n)^2,$$
--   and let $\Omega$ be drawn from the Bernoulli model with $p = m/n^2$. Then with probability at least $1 - n^{-3}$ both of the following hold:
--
--   1. the restriction of $\mathcal P_\Omega$ to the tangent space $T$ is injective;
--   2. the candidate certificate $Y$ of (III.10), namely the matrix of least Frobenius norm among those with $\mathcal P_\Omega(Y) = Y$ and $\mathcal P_T(Y) = E$, obeys
--   $$\|\mathcal P_{T^\perp}(Y)\| \le \tfrac12 .$$
--
--   In particular $Y$ satisfies conditions a)–c) of Lemma 3.1 (it is a dual certificate), and together with Lemma 3.1 this yields exact recovery by nuclear-norm minimization under the Bernoulli model.
--
--   **Formalization Note** The printed corollary assumes rank $r = O(1)$ and the sampling condition (I.10), $m \ge C\mu^4 n(\log n)^2$. Its proof derives the sufficient condition (III.26), $m \ge C_0 n r_\mu^2(\log n)^2/\sigma$ with $r_\mu = \mu^2 r$, which is the general-rank condition (I.11) that the paper states on p. 2055; this formalization states that general-rank form (for $r = O(1)$ it is the printed corollary). The certificate (III.10) is characterized through the platform predicate `LeastSquaresDualCertificate` (p. 2061 shows (III.10) is this minimizer); the injectivity in item 1 is the event on which (III.10) is defined. $\|\cdot\|$ is the spectral norm, $\log$ is natural, and only the square case is stated.
-- source:
--   Candès & Tao, The Power of Convex Relaxation: Near-Optimal Matrix Completion, IEEE Trans. Inf. Theory 56(5), 2010, p. 2063, Corollary 3.5 and its proof, Eq. (III.26); (III.10) and its least-squares characterization p. 2061; (I.11) p. 2055

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_CandesTao_Shared_StrongIncoherence

open MatrixCompletion

namespace CandesTao.CompletionI

/-- Candès–Tao, Corollary 3.5 (Existence of Dual Certificate I), general-rank form
(condition (I.11), as derived from (III.26)), square case.  There is an absolute constant
`C > 0` such that for every fixed `n × n` matrix `M` with rank-`r` SVD `S` obeying strong
incoherence with parameter `μ`, if `m ≤ n²` and `m ≥ C μ⁴ n r² (log n)²`, then under the
Bernoulli model with `p = m/n²`, with probability at least `1 - n⁻³` the restriction of
`P_Ω` to `T` is injective and the least-squares certificate `Y` of (III.10) (the
minimum-Frobenius-norm `Y` with `P_Ω(Y) = Y` and `P_T(Y) = E`) obeys
`‖P_{T⊥}(Y)‖ ≤ 1/2`; in particular `Y` is a dual certificate in the sense of Lemma 3.1. -/
theorem dual_certificate_existence_i :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n r m : ℕ) (M : RealMatrix n n) (S : SVD M r) (μ : ℝ),
        CandesTao.Shared.StrongIncoherence S μ →
        m ≤ n * n →
        C * μ ^ 4 * (n : ℝ) * (r : ℝ) ^ 2 * (Real.log (n : ℝ)) ^ 2 ≤ (m : ℝ) →
        1 - 1 / (n : ℝ) ^ 3 ≤
          bernoulliEventProb ((m : ℝ) / (n : ℝ) ^ 2)
            (fun Ω => SamplingOperatorInjectiveOnT Ω S ∧
              ∃ Y : RealMatrix n n, LeastSquaresDualCertificate Ω S Y ∧
                spectralNorm (normalProjection S Y) ≤ 1 / 2) := by sorry

end CandesTao.CompletionI
