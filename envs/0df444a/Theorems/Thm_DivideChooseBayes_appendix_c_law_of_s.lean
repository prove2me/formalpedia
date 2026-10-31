-- Prove2me | Theorems.Thm_DivideChooseBayes_appendix_c_law_of_s
-- name    : DivideChooseBayes.appendix_c_law_of_s
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:26:55.886984+00:00
-- url     : https://prove2.me/theorems/ffc2f3e3-bc04-4ad1-a9b5-3e903190cd6f
-- title:
--   Appendix C, p.32 — under normal priors $s=\sum_i g^C_i q_i \sim \mathcal N(\sum_i\mu_i q_i, \sum_i\sigma_i^2q_i^2)$ and $\Pr[s\ge 0]=\Phi(\cdot)$
-- statement:
--   Let the chooser's values be independent with $g^C_i\sim\mathcal N(\mu_i,\sigma_i^2)$, $\sigma_i>0$, and for $q\in\mathbb R^n$ let $s:=\sum_{i=1}^n g^C_i q_i$. Then
--
--   1. $s$ is normal with mean $\sum_i\mu_i q_i$ and variance $\sum_i\sigma_i^2q_i^2$;
--   2. if $q\ne 0$,
--   $$\Pr[s\ge 0]=\Pr[s>0]=\Phi\left(\frac{\sum_{i=1}^n\mu_i q_i}{\sqrt{\sum_{i=1}^n\sigma_i^2q_i^2}}\right),$$
--   where $\Phi$ is the standard normal cdf.
--
--   This turns the probability that the chooser picks pile 1 into the closed form behind the third constraint of $\mathcal C_P$.
--
--   Differences from the source:
--   - generalization: q the division computed on an iteration of Algorithm 1 → every q ∈ ℝⁿ; reason: the computation uses no constraint on q
--   - encoding: Pr[s ≥ 0] = Φ(Σᵢµᵢqᵢ/√(Σᵢσᵢ²qᵢ²)) → the formula for q ≠ 0; reason: at q = 0 the variance is 0 and the right-hand side Φ(0/0) is undefined (s = 0 surely)
--   - generalization: the formula for Pr[s ≥ 0] → the same formula for Pr[s ≥ 0] and for Pr[s > 0]; reason: s has a continuous law for q ≠ 0; dropping the second clause gives the source's statement
-- source:
--   Tucker-Foltz & Zeckhauser, Playing Divide-and-Choose Given Uncertain Preferences, arXiv:2207.03076v2, Appendix C, p.32

import Mathlib
import Definitions.Def_DivideChooseBayes_normalPrior
import Definitions.Def_fd06_standardNormalCDF

open MeasureTheory ProbabilityTheory

namespace DivideChooseBayes

/-- **Appendix C, p.32: the law of `s` and the probability that `s ≥ 0`.**
Tucker-Foltz & Zeckhauser, *Playing Divide-and-Choose Given Uncertain Preferences*,
arXiv:2207.03076v2, Appendix C, p.32: "Since each gᶜᵢ follows a normal distribution with mean µᵢ and
variance σᵢ², we know that s follows a normal distribution with mean ∑ᵢ µᵢqᵢ and variance
∑ᵢ σᵢ²qᵢ². Hence, the probability that s ≥ 0 is given by
1 − Φ((0 − ∑ᵢ µᵢqᵢ)/√(∑ᵢ σᵢ²qᵢ²)) = Φ(∑ᵢ µᵢqᵢ/√(∑ᵢ σᵢ²qᵢ²))", where `s := ∑ᵢ gᶜᵢqᵢ`.

Under independent normal priors `N(mᵢ, σᵢ²)` with `σᵢ > 0`, for every `q ∈ ℝⁿ` the law of
`s = ∑ᵢ gᶜᵢqᵢ` is `N(∑ᵢ mᵢqᵢ, ∑ᵢ σᵢ²qᵢ²)`; and for `q ≠ 0`,
`Pr[s ≥ 0] = Pr[s > 0] = Φ(∑ᵢ mᵢqᵢ / √(∑ᵢ σᵢ²qᵢ²))`.

**Formalization Note.** For `q = 0` the variance vanishes, `s = 0`, and the right-hand side is the
undefined `Φ(0/0)` (in Lean `Φ(0) = 1/2`), so the formula is stated for `q ≠ 0`. `N(m, 0)` is the
Dirac mass. -/
theorem appendix_c_law_of_s {ι : Type*} [Fintype ι] (m σ : ι → ℝ) (hσ : ∀ i, 0 < σ i)
    (q : ι → ℝ) :
    (normalPrior m σ).map (fun gC => ∑ i, gC i * q i) =
        gaussianReal (∑ i, m i * q i) (∑ i, σ i ^ 2 * q i ^ 2).toNNReal ∧
      (q ≠ 0 →
        (normalPrior m σ).real {gC | 0 ≤ ∑ i, gC i * q i} =
            FinancialDerivatives.FD06.standardNormalCDF
              ((∑ i, m i * q i) / Real.sqrt (∑ i, σ i ^ 2 * q i ^ 2)) ∧
          (normalPrior m σ).real {gC | 0 < ∑ i, gC i * q i} =
            FinancialDerivatives.FD06.standardNormalCDF
              ((∑ i, m i * q i) / Real.sqrt (∑ i, σ i ^ 2 * q i ^ 2))) := by sorry

end DivideChooseBayes
