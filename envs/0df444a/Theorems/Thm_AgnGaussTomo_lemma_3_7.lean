-- Prove2me | Theorems.Thm_AgnGaussTomo_lemma_3_7
-- name    : AgnGaussTomo.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:22:40.915355+00:00
-- url     : https://prove2.me/theorems/78686c30-8818-4ab8-8ed0-26633d7edcac
-- title:
--   Lemma 3.7 — pure-state projection of heterodyne estimates
-- statement:
--   There are universal constants $C>0$ and $\zeta_0>0$ such that the following holds. Let $|\psi\rangle\langle\psi|=\pi(m,V)$ be a pure Gaussian state of $n$ modes with mean $m$ and covariance $V$, $\|V^{-1}\|_{\mathrm{op}}\le2$, and let $\mu_h=m$, $\Sigma_h=(I+V)/2$ be the mean and covariance of its heterodyne outcome distribution. Let $0\le\zeta\le\zeta_0$ and let $(\hat\mu_h,\hat\Sigma_h)$ satisfy
--
--   $$
--   \|\hat\mu_h-\mu_h\|_2\le\zeta,\qquad\|\hat\Sigma_h-\Sigma_h\|_F\le\zeta .
--   $$
--
--   For any Williamson decomposition $\hat V_{\mathrm{raw}}=2\hat\Sigma_h-I=\hat S\hat D\hat S^\top$, put $\hat V=\hat S\hat S^\top$, and let $|\hat\psi\rangle\langle\hat\psi|=\pi(\hat\mu_h,\hat V)$ be the (pure) Gaussian state with mean $\hat\mu_h$ and covariance $\hat V$. Then
--
--   $$
--   d_{\mathrm{tr}}\big(|\hat\psi\rangle\langle\hat\psi|,|\psi\rangle\langle\psi|\big)\le C\,\zeta .
--   $$
--
--   Replacing all symplectic eigenvalues of the estimated covariance by $1$ thus projects accurate heterodyne moments onto a nearby pure Gaussian state, with no dependence on $n$.
--
--   Differences from the source:
--   - reading: ≲ and "ζ sufficiently small" → universal constants chosen before n and every other parameter; reason: the paper calls them universal constants; ≲ and O hide absolute constants
--   - generalization: V̂ = ŜŜᵀ from the decomposition of V̂_raw, and the estimate π(μ̂_h, V̂) → every Williamson decomposition of V̂_raw and every state with mean μ̂_h and covariance ŜŜᵀ; reason: specializes to the paper's choice of decomposition and of π(μ̂_h, V̂)
--   - encoding: ζ → 0 ≤ ζ; reason: a bound on norms; negative ζ makes the hypotheses unsatisfiable
--   - encoding: trace distances → the published BosonicLearn.traceDist (½‖·‖₁) in ℝ≥0∞, compared with ENNReal.ofReal of the bound; reason: same values on density operators
--   - encoding: covariances and means in the order (q₁, …, qₙ, p₁, …, pₙ) → the interleaved order (q₁, p₁, …, qₙ, pₙ) of the published GaussianAt, with symplectic and Williamson data in the grouped order; reason: a relabelling of the same quadratures; norms, traces and the Loewner order are unchanged
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), Lemma 3.7, printed p. 17 (PDF p. 20); proof in App. A.2.3

import Mathlib
import Definitions.Def_OptGaussTomo_boseGauss
import Definitions.Def_BosonicLearn_traceDist
import Definitions.Def_AgnGaussTomo_grouped
import Definitions.Def_AgnGaussTomo_IsWilliamson
import Definitions.Def_AgnGaussTomo_opNorm
import Definitions.Def_AgnGaussTomo_frobNorm

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14 (GaussianAt InterleavedQuadrature OscillatorCovariance)

namespace AgnGaussTomo

/-- **Lemma 3.7: pure-state projection of the heterodyne estimates.** Arulandu, Chen, Chen, Li, Ma,
*Finding Gaussian Structure in Bosonic States*, arXiv:2610.06810 (version of 3 Nov 2026), Lemma 3.7,
printed p. 17 (PDF p. 20): "Suppose ‖V^{-1}‖_op ≤ 2 and that there exist estimators (μ̂_h, Σ̂_h) which
satisfy ‖μ̂_h − μ_h‖₂ ≤ ζ, ‖Σ̂_h − Σ_h‖_F ≤ ζ (20) where μ_h = m and Σ_h = (I+V)/2 denote the parameters
of the heterodyne outcome distribution for pure Gaussian state |ψ⟩⟨ψ| = π(m, V). Define the estimate
|ψ̂⟩⟨ψ̂| ≡ π(μ̂_h, V̂) where V̂ = ŜŜᵀ from the decomposition of V̂_raw ≡ 2Σ̂_h − I = ŜD̂Ŝᵀ. Then,
d_tr(|ψ̂⟩⟨ψ̂|, |ψ⟩⟨ψ|) ≲ ζ provided that ζ is sufficiently small."

**Formalization Note.** "≲" and "sufficiently small" are universal constants `C`, `ζ₀` chosen before
`n`. The statement holds for **every** Williamson decomposition `Ŝ D̂ Ŝᵀ` of `V̂_raw` (in the grouped
ordering) and every state with mean `μ̂_h` and covariance `V̂ = ŜŜᵀ` (`π(μ̂_h, V̂)`), so neither existence
nor uniqueness of the decomposition is assumed. Covariances use the vacuum-`I` normalization of the
published `GaussianAt`. -/
theorem lemma_3_7 : ∃ C : ℝ, 0 < C ∧ ∃ ζ₀ : ℝ, 0 < ζ₀ ∧
    ∀ (n : ℕ) (ψ : State (Occupation (Fin n))) (m : InterleavedQuadrature (Fin n) → ℝ)
      (V : OscillatorCovariance (Fin n)),
      ψ ∈ OptGaussTomo.bosePure n → GaussianAt ψ.coefficients m V → opNorm V⁻¹ ≤ 2 →
      ∀ ζ : ℝ, 0 ≤ ζ → ζ ≤ ζ₀ →
      ∀ (μhat : InterleavedQuadrature (Fin n) → ℝ) (Sigmahat : OscillatorCovariance (Fin n)),
        Real.sqrt (∑ a, (μhat a - m a) ^ 2) ≤ ζ →
        frobNorm (Sigmahat - (1 / 2 : ℝ) • (1 + V)) ≤ ζ →
        ∀ (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (d : Fin n → ℝ),
          IsWilliamson (grouped ((2 : ℝ) • Sigmahat - 1)) S d →
          ∀ (Vhat : OscillatorCovariance (Fin n)), grouped Vhat = S * S.transpose →
          ∀ ψhat : State (Occupation (Fin n)), GaussianAt ψhat.coefficients μhat Vhat →
            BosonicLearn.traceDist ψhat.coefficients ψ.coefficients ≤ ENNReal.ofReal (C * ζ) := by sorry

end AgnGaussTomo
