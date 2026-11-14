-- Prove2me | Theorems.Thm_BosonicLearn_eq_207
-- name    : BosonicLearn.eq_207
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T07:28:53.934201+00:00
-- url     : https://prove2.me/theorems/0168decc-6a98-4f02-8f06-02971a2888df
-- title:
--   Eq. (207) — heterodyne detection on $\rho(\mu,\Sigma)$ yields $\mathcal N(\mu,\Sigma+\tfrac12I)$
-- statement:
--   Let $\rho=\rho(\mu,\Sigma)$ be an $n$-mode Gaussian state (grouped quadratures, vacuum covariance $\tfrac12I$). The outcome $Y\in\mathbb R^{2n}$ of heterodyne detection on $\rho$, whose law has density $Q_\rho(\beta)=(2\pi)^{-n}\langle\alpha(\beta)|\rho|\alpha(\beta)\rangle$, is Gaussian:
--
--   $$Y\sim\mathcal N(\mu,C),\qquad C:=\Sigma+\tfrac12 I .$$
--
--   This is the starting point of heterodyne tomography: learning $\rho$ reduces to estimating the mean and covariance of a classical Gaussian. The paper takes it from [BMEM25, Eq. (39)].
--
--   Differences from the source:
--   - encoding: the heterodyne outcome law N(µ, Σ + ½I) → the measure with density (2π)^{-n}⟨α(β)|ρ|α(β)⟩ equals Mathlib's multivariateGaussian on EuclideanSpace ℝ (Fin n ⊕ Fin n); reason: same law; equality of measures also fixes the normalization
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §7.2, Eq. (207), p. 61

import Mathlib
import Definitions.Def_BosonicLearn_heterodyneLaw
import Definitions.Def_BosonicLearn_IsGaussianState
open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **Eq. (207) — heterodyne detection on `ρ(µ, Σ)` yields `N(µ, Σ + ½I)`.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §7.2, proof of Theorem 8, Eq. (207), p. 61: "In our covariance convention, a heterodyne measurement on
ρ(µ, Σ) produces a classical Gaussian outcome Y ∼ N(µ, C), C := Σ + 1/2 I. This is the standard heterodyne law
[BMEM25, Eq. (39)], after the fixed permutation from the interleaved quadrature ordering used there to the grouped
ordering used in this manuscript."

For every `n`-mode Gaussian state `ρ(µ, Σ)` (grouped quadratures, vacuum `Σ = ½I`), the heterodyne outcome law,
defined from the Husimi density `(2π)^{-n}⟨α(β)|ρ|α(β)⟩`, equals the multivariate Gaussian measure on `ℝ²ⁿ`
with mean `µ` and covariance `Σ + ½I`.

**Formalization Note.** Mathlib's `multivariateGaussian` is the Gaussian law on `EuclideanSpace ℝ (Fin n ⊕ Fin n)`.
The paper imports this identity from [BMEM25]; equality of measures also says the Husimi density has total mass one. -/
theorem eq_207 {n : ℕ} (ρ : State (Occupation (Fin n))) (μ : Fin n ⊕ Fin n → ℝ)
    (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (hρ : IsGaussianState ρ μ S) :
    heterodyneLaw ρ.coefficients = multivariateGaussian (WithLp.toLp 2 μ) (S + (1 / 2 : ℝ) • 1) := by sorry

end BosonicLearn
