-- Prove2me | Theorems.Thm_CandesTao_CompletionII_replacing_tangent_projection
-- name    : CandesTao.CompletionII.replacing_tangent_projection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:55:03.210228+00:00
-- url     : https://prove2.me/theorems/d8a44a34-1191-4ff6-8cc4-8abd240ffc1c
-- title:
--   Lemma 3.3 — Replacing $\mathcal{P}_T$ with $\mathcal{Q}_T$
-- statement:
--   Let $M \in \mathbb{R}^{n\times n}$ have a rank-$r$ SVD with sign matrix $E$ and tangent-space projection $\mathcal{P}_T$. Let $2nr \le m \le n^2$ (the standing assumption (I.22)), $p := m/n^2$, $\mathcal{Q}_\Omega := p^{-1}\mathcal{P}_\Omega - \mathcal{I}$ and $\mathcal{Q}_T := \mathcal{P}_T - \rho'\mathcal{I}$ with $\rho' = 2r/n - (r/n)^2$. Let $0 < \sigma < 1$ with
--   $$\frac{8nr}{m} < \sigma^{3/2},$$
--   and let $k_0 \ge 0$. Suppose that the observation set $\Omega$ lies in the event
--   $$\left\|(\mathcal{Q}_\Omega\mathcal{Q}_T)^k\mathcal{Q}_\Omega(E)\right\| \le \sigma^{\frac{k+1}{2}} \quad \text{for all } 0 \le k < k_0. \qquad \text{(III.18)}$$
--   Then for all $0 \le k < k_0$,
--   $$\left\|(\mathcal{Q}_\Omega\mathcal{P}_T)^k\mathcal{Q}_\Omega(E)\right\| \le \left(1 + 4^{k+1}\right)\sigma^{\frac{k+1}{2}}. \qquad \text{(III.19)}$$
--   Here $\|\cdot\|$ is the spectral norm.
--
--   The lemma lets the analysis bound the Neumann-series terms, which involve $\mathcal{P}_T$, through the moments of $(\mathcal{Q}_\Omega\mathcal{Q}_T)^k\mathcal{Q}_\Omega(E)$ (Theorem 3.6).
--
--   **Formalization Note** The statement is deterministic: the event (III.18) is a hypothesis on the fixed set $\Omega$, and the conclusion holds for that $\Omega$. No incoherence assumption is needed.
-- source:
--   Candès & Tao, The Power of Convex Relaxation: Near-Optimal Matrix Completion, IEEE Trans. Inf. Theory 56(5), 2010, p. 2062, Lemma 3.3, Eqs. (III.18), (III.19); proof in Appendix A, pp. 2078–2080

import Definitions.Def_CandesTao_CompletionII_CenteredOperators

open MatrixCompletion

namespace CandesTao.CompletionII

/-- Candès–Tao, Lemma 3.3 (Replacing `P_T` with `Q_T`), square case, deterministic in
`Ω`.  Let `M` be an `n × n` real matrix with rank-`r` SVD `S` and sign matrix `E`, let
`2nr ≤ m ≤ n²` (standing assumption (I.22)), `p := m/n²`, `Q_Ω := p⁻¹ P_Ω - 𝓘`,
`Q_T := P_T - ρ' 𝓘`, and let `0 < σ < 1` with `8nr/m < σ^{3/2}`.  For every observation
set `Ω` on which the event (III.18)
`‖(Q_Ω Q_T)^k Q_Ω(E)‖ ≤ σ^{(k+1)/2}` for all `0 ≤ k < k₀`
holds, we have for all `0 ≤ k < k₀` (III.19)
`‖(Q_Ω P_T)^k Q_Ω(E)‖ ≤ (1 + 4^{k+1}) σ^{(k+1)/2}`.
Norms are spectral norms. -/
theorem replacing_tangent_projection (n r m : ℕ) (M : RealMatrix n n) (S : SVD M r)
    (Ω : Finset (Fin n × Fin n)) (σ : ℝ) (k₀ : ℕ)
    (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hI22 : 2 * n * r ≤ m) (hmn : m ≤ n * n)
    (hproviso : 8 * (n : ℝ) * (r : ℝ) / (m : ℝ) < σ ^ ((3 : ℝ) / 2))
    (hevent : ∀ k < k₀,
      spectralNorm (momentMatrix S Ω ((m : ℝ) / (n : ℝ) ^ 2) k) ≤
        σ ^ (((k : ℝ) + 1) / 2)) :
    ∀ k < k₀,
      spectralNorm (tangentPower S Ω ((m : ℝ) / (n : ℝ) ^ 2) k
          (centeredSamplingFluctuation Ω ((m : ℝ) / (n : ℝ) ^ 2) (signMatrix S))) ≤
        (1 + 4 ^ (k + 1)) * σ ^ (((k : ℝ) + 1) / 2) := by sorry

end CandesTao.CompletionII
