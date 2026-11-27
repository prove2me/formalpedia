-- Prove2me | Theorems.Thm_BosonicResources_gaussian_measurement_law
-- name    : BosonicResources.gaussian_measurement_law
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-27T05:48:13.642235+00:00
-- url     : https://prove2.me/theorems/e33a67ca-05a3-53b5-b60c-92cd53cb5ade
-- title:
--   Outcome law of a Gaussian measurement on a Gaussian state: $\mathcal N(\mu,\Sigma+V)$
-- statement:
--   Here $\rho(\mu,\Sigma)$ denotes the $n$-mode Gaussian state with mean $\mu\in\mathbb R^{2n}$ and covariance matrix $\Sigma$, a real $2n\times 2n$ matrix (quadratures ordered $(x_1,\dots,x_n,p_1,\dots,p_n)$, vacuum covariance $\tfrac12 I$). Further, $\mathcal N(m,C)$ denotes the Gaussian probability measure on $\mathbb R^{2n}$ with mean $m$ and covariance $C$. A *Gaussian (general-dyne) measurement with seed covariance $V$* is the POVM on one copy with outcomes $\xi\in\mathbb R^{2n}$ and elements $(2\pi)^{-n}\rho(\xi,V)\,d\xi$, the displaced copies of a Gaussian seed state with covariance $V$.
--
--   Let $V$ be a real $2n\times2n$ matrix, let $P$ be a Gaussian measurement with seed covariance $V$ on an $n$-mode system, and let $\rho(\mu,\Sigma)$ be an $n$-mode Gaussian state. Then the outcome $\xi\in\mathbb R^{2n}$ of $P$ on $\rho(\mu,\Sigma)$ has the distribution
--
--   $$
--   \xi\ \sim\ \mathcal N(\mu,\ \Sigma+V).
--   $$
--
--   This is the rule by which the paper computes the statistics of Gaussian measurements on Gaussian states: the measurement returns a sample of the Wigner distribution $\mathcal N(\mu,\Sigma)$ with the seed covariance added as noise. For heterodyne detection ($V=\tfrac12 I$) it gives $\mathcal N(\mu,\Sigma+\tfrac12 I)$. The rule is used throughout the paper, for instance in App. B.1 (Lemma B.1), in the heterodyne lower bound (Theorem S7) and in the analysis of the non-adaptive protocol of Theorem 7 (App. E.2).
--
--   **Formalization Note** For $V=\tfrac12 I$ (heterodyne) this is Eq. (207) of arXiv:2609.26705, published and proved as `BosonicLearn.eq_207` for the Husimi-density form of the heterodyne law. The outcome distribution is the Born law of the POVM (`FockPOVM.law`), and the conclusion is an equality of measures with Mathlib's `multivariateGaussian`. The hypothesis is `IsGaussianMeasurement P V`, in which outcomes are labelled so that the POVM element at $\xi$ is $(2\pi)^{-n}\rho(\xi,V)$; no separate assumption on $V$ is made (if $V$ is not a valid covariance matrix, no such $P$ exists).
-- source:
--   Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, What resources are needed for optimal learning of bosonic Gaussian states?, https://arxiv.org/abs/2603.18136, Sec. 2 (outcome distribution of a Gaussian measurement); used in App. B.1, Eq. (S26) step (i), in App. C.3, proof of Theorem S7, and in App. E.2, Eq. (S164)

import Mathlib
import Definitions.Def_BosonicLearn_IsGaussianState
import Definitions.Def_BosonicResources_IsGaussianMeasurement
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open BosonicLearn

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicResources

/-- **Outcome law of a Gaussian measurement on a Gaussian state: `N(µ, Σ + V)`.**
Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, *What resources are needed for optimal learning of bosonic
Gaussian states?*, arXiv:2603.18136, §2: "The outcome distribution obtained by applying a Gaussian measurement with seed covariance matrix V on a
Gaussian state ρ(µ,Σ) is given by N(µ, Σ+V)." Used throughout, e.g. Eq. (S26) step (i), Eq. (S164), and in the
heterodyne case `V = ½I` in the proof of Theorem S7 ("N(0, Σ_a + ½ I_{2n})").

If `P` is a Gaussian measurement with seed covariance `V` on the `n`-mode Fock space and `ρ` is the Gaussian state
`ρ(µ, Σ)`, then the Born outcome law of `P` on `ρ` is the multivariate Gaussian measure on `ℝ²ⁿ` with mean `µ` and
covariance `Σ + V`.

**Formalization Note.** For `V = ½I` (heterodyne) this is Eq. (207) of arXiv:2609.26705, published and proved as
`BosonicLearn.eq_207` for the Husimi-density form of the heterodyne law. -/
theorem gaussian_measurement_law {n : ℕ}
    (P : FockPOVM (Occupation (Fin n)) (EuclideanSpace ℝ (Fin n ⊕ Fin n)))
    (V : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (hP : IsGaussianMeasurement P V)
    (ρ : State (Occupation (Fin n))) (μ : Fin n ⊕ Fin n → ℝ)
    (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (hρ : IsGaussianState ρ μ S) :
    P.law ρ.coefficients = multivariateGaussian (WithLp.toLp 2 μ) (S + V) := by sorry

end BosonicResources
