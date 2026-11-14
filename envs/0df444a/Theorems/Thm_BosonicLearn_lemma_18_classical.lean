-- Prove2me | Theorems.Thm_BosonicLearn_lemma_18_classical
-- name    : BosonicLearn.lemma_18_classical
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T21:38:59.076202+00:00
-- url     : https://prove2.me/theorems/1977e4a4-a87c-4ba4-a26c-d07d6556f40b
-- title:
--   Lemma 18 for $\Sigma\succeq\tfrac12I$ with constant $1/\sqrt2$: $\tfrac12\|\rho(\mu',\Sigma)-\rho(\mu,\Sigma)\|_1\le\tfrac1{\sqrt2}\|\Sigma^{-1/2}(\mu'-\mu)\|_2$
-- statement:
--   A first-moment perturbation bound for Gaussian states with classical covariance, proved without the Gaussian fidelity formula.
--
--   Let $\Sigma$ be a covariance matrix with $\Sigma\succeq\tfrac12\mathbf 1$ and let $\rho(\mu,\Sigma)$, $\rho(\mu',\Sigma)$ be Gaussian states. Then
--
--   $$
--   \tfrac12\big\|\rho(\mu',\Sigma)-\rho(\mu,\Sigma)\big\|_1\ \le\ \frac1{\sqrt2}\sqrt{(\mu'-\mu)^T\Sigma^{-1}(\mu'-\mu)} .
--   $$
--
--   Comparison with Lemma 18 of the paper (`BosonicLearn.lemma_18`): same right-hand side up to the constant ($\tfrac1{\sqrt2}$ instead of $\tfrac12$), under the extra hypothesis $\Sigma\succeq\tfrac12\mathbf 1$. Both tomography theorems (Theorem 8 and [BMEM25, Theorem 10]) assume $\Sigma\succeq\tfrac12\mathbf 1$ and have unspecified constants, so this version suffices there.
--
--   Proof idea. $\rho(\mu,\Sigma)$ is a mixture of coherent states over $\mathcal N(\mu,\Sigma-\tfrac12\mathbf 1)$. The shift $\delta=\mu'-\mu$ is split as $(\Sigma-\tfrac12)\Sigma^{-1}\delta$, absorbed in the mixing measure at total-variation cost $\le\sqrt A/\sqrt{2\pi}$, plus $\tfrac12\Sigma^{-1}\delta$, a displacement of the coherent states at cost $\le\sqrt B/2$, where $A+B=\delta^T\Sigma^{-1}\delta$.
--
--   **Formalization Note** Same formal shape as `BosonicLearn.lemma_18`, with the hypothesis `(S - (1/2) • 1).PosSemidef` and the bound `ENNReal.ofReal (Real.sqrt (…) / Real.sqrt 2)`.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Lemma 18 (first-moment perturbation), Eq. (204), p. 60

import Mathlib
import Definitions.Def_BosonicLearn_traceDist
import Definitions.Def_BosonicLearn_IsGaussianState

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open MeasureTheory
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **Lemma 18 for classical covariances, with constant `1/√2`.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Lemma 18 (first-moment perturbation), Eq. (204), p. 60: "For every valid covariance matrix Σ and all µ, µ′ ∈ ℝ^{2n},
½‖ρ(µ′, Σ) − ρ(µ, Σ)‖₁ ≤ ½‖Σ^{−1/2}(µ′ − µ)‖₂."

If `Σ ⪰ ½I`, then for Gaussian states `ρ(µ, Σ)` and `ρ(µ′, Σ)`,
`½‖ρ(µ′, Σ) − ρ(µ, Σ)‖₁ ≤ (1/√2) √((µ′ − µ)ᵀ Σ⁻¹ (µ′ − µ))`.

**Formalization Note.** Same statement as `lemma_18` except for the hypothesis `Σ − ½I ⪰ 0` and the constant `1/√2`
in place of `½`. It is proved without the Gaussian fidelity formula: `ρ(µ, Σ)` is a mixture of coherent states over
`N(µ, Σ − ½I)`; the shift `δ = µ′ − µ` is split as `(Σ − ½I)Σ⁻¹δ` (absorbed in the mixing measure, total variation
cost) plus `½Σ⁻¹δ` (a displacement of the coherent states). The promise `Σ ⪰ ½I` holds in Theorem 8 and in
[BMEM25, Theorem 10], and the weaker constant is absorbed in their constants. -/
theorem lemma_18_classical {n : ℕ} (ρ ρ' : State (Occupation (Fin n))) (μ μ' : Fin n ⊕ Fin n → ℝ)
    (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (hS : (S - (1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)).PosSemidef)
    (h : IsGaussianState ρ μ S) (h' : IsGaussianState ρ' μ' S) :
    traceDist ρ'.coefficients ρ.coefficients ≤
      ENNReal.ofReal (Real.sqrt ((μ' - μ) ⬝ᵥ (S⁻¹ *ᵥ (μ' - μ))) / Real.sqrt 2) := by sorry

end BosonicLearn
