-- Prove2me | Theorems.Thm_CPDETrial_argmax_unique
-- name    : CPDETrial.argmax_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:23:55.694032+00:00
-- url     : https://prove2.me/theorems/7718542e-3496-4867-bc93-5d33a28136c9
-- title:
--   The best arm is almost surely unique
-- statement:
--   Let $M\ge2$ and let $\theta$ be a random vector in $\mathbb R^M$ with law $N(\mu^0,\Sigma^0)$, $\Sigma^0$ positive definite. Then with probability one there is an arm $i$ with
--
--   $$
--   \theta_j<\theta_i\quad\text{for every } j\ne i,
--   $$
--
--   that is, $\arg\max_i\theta_i$ is uniquely defined (no ties). This is the last step of the proof of Theorem 1.
--
--   Differences from the source:
--   - encoding: arg max{θ_i} is uniquely defined (no ties) with probability 1 → almost surely ∃ i, ∀ j ≠ i, θ_j < θ_i; reason: same statement
-- source:
--   Chick, Gans & Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN preprint 3184758 (version of August 31, 2020), p. ec7, proof of Theorem 1 (unnumbered)

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CPDETrial

/-- **The best arm is almost surely unique.**
Chick, Gans & Yapar, *Bayesian Sequential Learning for Clinical Trials of Multiple Correlated
Medical Interventions*, SSRN preprint 3184758 (version of August 31, 2020), proof of Theorem 1, p. ec7 (unnumbered): "The normality of the positive definite prior
`Σ⁰` implies that `arg max{θ_i}` is uniquely defined (no ties) with probability 1."

If `θ` has the law `N(µ⁰, Σ⁰)` on `ℝ^M`, `M ≥ 2`, with `Σ⁰` positive definite, then almost
surely some arm `i` has `θ_j < θ_i` for every `j ≠ i`.

**Formalization Note.** `µ⁰ : Fin M → ℝ` enters Mathlib's `multivariateGaussian` through
`WithLp.toLp 2`. The law hypothesis forces `θ` to be almost everywhere measurable (`Measure.map`
of a non-measurable map is `0`), so no separate measurability hypothesis is needed. -/
theorem argmax_unique {M : ℕ} (hM : 2 ≤ M) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (mu0 : Fin M → ℝ)
    (Sig0 : Matrix (Fin M) (Fin M) ℝ) (hSig0 : Sig0.PosDef)
    (θ : Ω → EuclideanSpace ℝ (Fin M))
    (hlaw : P.map θ = multivariateGaussian (WithLp.toLp 2 mu0) Sig0) :
    ∀ᵐ ω ∂P, ∃ i, ∀ j, j ≠ i → θ ω j < θ ω i := by sorry

end CPDETrial
