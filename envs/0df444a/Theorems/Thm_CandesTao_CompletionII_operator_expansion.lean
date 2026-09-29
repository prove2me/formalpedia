-- Prove2me | Theorems.Thm_CandesTao_CompletionII_operator_expansion
-- name    : CandesTao.CompletionII.operator_expansion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:54:19.216545+00:00
-- url     : https://prove2.me/theorems/530db2a5-523d-4b1f-bfaf-9c87cf25a115
-- title:
--   Lemma 8.1 — Expansion of $(\mathcal{Q}_\Omega\mathcal{P}_T)^k\mathcal{Q}_\Omega$ in powers of $\mathcal{Q}_\Omega\mathcal{Q}_T$
-- statement:
--   Let $M \in \mathbb{R}^{n\times n}$ have a rank-$r$ SVD with tangent-space projection $\mathcal{P}_T$. Let $0 < m \le n^2$, $p := m/n^2$, $\rho' := 2r/n - (r/n)^2$, and for an observation set $\Omega$ let $\mathcal{Q}_\Omega := p^{-1}\mathcal{P}_\Omega - \mathcal{I}$ and $\mathcal{Q}_T := \mathcal{P}_T - \rho'\mathcal{I}$. Let $\alpha^{(k)}, \beta^{(k)}, \gamma^{(k)}, \delta^{(k)}$ be the coefficient sequences of Lemma 8.1 for these $p$ and $\rho'$.
--
--   Then for every $\Omega$ and every $k \ge 0$, as operators on $\mathbb{R}^{n\times n}$,
--   $$(\mathcal{Q}_\Omega\mathcal{P}_T)^k\mathcal{Q}_\Omega = \sum_{j=0}^{k}\alpha_j^{(k)}(\mathcal{Q}_\Omega\mathcal{Q}_T)^j\mathcal{Q}_\Omega + \sum_{j=0}^{k-1}\beta_j^{(k)}(\mathcal{Q}_\Omega\mathcal{Q}_T)^j + \sum_{j=0}^{k-2}\gamma_j^{(k)}\mathcal{Q}_T(\mathcal{Q}_\Omega\mathcal{Q}_T)^j\mathcal{Q}_\Omega + \sum_{j=0}^{k-3}\delta_j^{(k)}\mathcal{Q}_T(\mathcal{Q}_\Omega\mathcal{Q}_T)^j.$$
--
--   The identity is deterministic. It rewrites the terms of the Neumann series for the dual certificate, which involve $\mathcal{P}_T$, in terms of the better-behaved centered operator $\mathcal{Q}_T$. Lemma 3.3 is proved from it.
--
--   **Formalization Note** The identity is stated applied to an arbitrary matrix $X$. Empty sums (for $k < 1, 2, 3$) are zero, via natural-number subtraction in `Finset.range (k - 1)` and `Finset.range (k - 2)`. The hypothesis $0 < m$ makes $p > 0$.
-- source:
--   Candès & Tao, The Power of Convex Relaxation: Near-Optimal Matrix Completion, IEEE Trans. Inf. Theory 56(5), 2010, p. 2078, Lemma 8.1, Eq. (VIII.2)

import Definitions.Def_CandesTao_CompletionII_CenteredOperators
import Definitions.Def_CandesTao_CompletionII_ExpansionCoefficients

open MatrixCompletion

namespace CandesTao.CompletionII

/-- Candès–Tao, Lemma 8.1 (identity (VIII.2)), square case.  Let `M` be an `n × n` real
matrix with rank-`r` SVD `S`, let `0 < m ≤ n²`, `p := m/n²`, `ρ' := 2(r/n) - (r/n)²`,
`Q_Ω := p⁻¹ P_Ω - 𝓘` and `Q_T := P_T - ρ' 𝓘`.  For every observation set `Ω`, every
`k ≥ 0` and every matrix `X`,
`(Q_Ω P_T)^k Q_Ω X = ∑_{j=0}^{k} α^{(k)}_j (Q_Ω Q_T)^j Q_Ω X + ∑_{j=0}^{k-1} β^{(k)}_j (Q_Ω Q_T)^j X
   + ∑_{j=0}^{k-2} γ^{(k)}_j Q_T (Q_Ω Q_T)^j Q_Ω X + ∑_{j=0}^{k-3} δ^{(k)}_j Q_T (Q_Ω Q_T)^j X`,
with the coefficient sequences of `expansionCoeffs p ρ'`. -/
theorem operator_expansion (n r m : ℕ) (M : RealMatrix n n) (S : SVD M r)
    (Ω : Finset (Fin n × Fin n)) (k : ℕ) (X : RealMatrix n n)
    (hm : 0 < m) (hmn : m ≤ n * n) :
    let p : ℝ := (m : ℝ) / (n : ℝ) ^ 2
    let c := expansionCoeffs p (rhoPrime n r) k
    tangentPower S Ω p k (centeredSamplingFluctuation Ω p X) =
      (∑ j ∈ Finset.range (k + 1),
          c.α j • centeredPower S Ω p j (centeredSamplingFluctuation Ω p X)) +
        (∑ j ∈ Finset.range k, c.β j • centeredPower S Ω p j X) +
        (∑ j ∈ Finset.range (k - 1),
          c.γ j • centeredTangentProjection S
            (centeredPower S Ω p j (centeredSamplingFluctuation Ω p X))) +
        (∑ j ∈ Finset.range (k - 2),
          c.δ j • centeredTangentProjection S (centeredPower S Ω p j X)) := by sorry

end CandesTao.CompletionII
