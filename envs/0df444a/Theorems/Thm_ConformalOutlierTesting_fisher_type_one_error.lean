-- Prove2me | Theorems.Thm_ConformalOutlierTesting_fisher_type_one_error
-- name    : ConformalOutlierTesting.fisher_type_one_error
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:56:02.663812+00:00
-- url     : https://prove2.me/theorems/0da7390b-ac12-4db4-8905-1a4e4162d20b
-- title:
--   Theorem 1: type-I error of Fisher's combination test
-- statement:
--   Let the scores be continuously distributed with law $\mu$, and assume the global null: the $m$ test scores and the $n$ calibration scores are all i.i.d. with law $\mu$. Let $m=\lfloor\gamma n\rfloor$ with $\gamma\in(0,\infty)$, and let $\alpha\in(0,1)$. As $n\to\infty$:
--
--   1. The type-I error of Fisher's combination test applied to the marginal conformal p-values satisfies
--   $$\mathbb P\Big[-2\sum_{i=1}^m\log\hat u^{(\mathrm{marg})}(X_{2n+i})\ge\chi^2(2m;1-\alpha)\Big]\to\bar\Phi\Big(\frac{z_{1-\alpha}}{\sqrt{1+\gamma}}\Big).$$
--   2. The conditional type-I error given the calibration data converges in distribution:
--   $$\mathbb P\Big[-2\sum_{i=1}^m\log\hat u^{(\mathrm{marg})}(X_{2n+i})\ge\chi^2(2m;1-\alpha)\,\Big|\,\mathcal D\Big]\xrightarrow{d}\bar\Phi(z_{1-\alpha}+\sqrt\gamma\,W),\qquad W\sim N(0,1).$$
--
--   Since $\gamma>0$, the limiting type-I error exceeds $\alpha$ whenever $\alpha<1/2$. So the dependence induced by the shared calibration set invalidates Fisher's test.
--
--   **Formalization Note** The level is restricted to $\alpha\in(0,1)$, which is implicit in the paper. Convergence in distribution is stated as convergence of $\mathbb E f(\cdot)$ for every bounded continuous $f$. Because the test scores are independent of $\mathcal D$, the conditional probability is written as the probability over the test scores with the calibration scores held fixed.
-- source:
--   Bates, Candès, Lei, Romano and Sesia, Testing for Outliers with Conformal p-values, arXiv:2104.08279v3 (2022), Section 2.1, Theorem 1, eq. (5), p. 6; proof in Appendix A.2 (Theorem 6 with ξ = 1), pp. 33-38

import Mathlib
import Definitions.Def_ConformalOutlierTesting_Basic

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction

namespace ConformalOutlierTesting

theorem fisher_type_one_error (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (γ : ℝ) (hγ : 0 < γ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    Tendsto (fun n : ℕ =>
        ((scoreLaw (n := n) μ (fun _ : Fin ⌊γ * (n : ℝ)⌋₊ => μ))
          {ω | quantile (chiSqLaw (2 * ⌊γ * (n : ℝ)⌋₊)) (1 - α) ≤ fisherStat ω.1 ω.2}).toReal)
      atTop (𝓝 (normSurv (quantile stdNormal (1 - α) / Real.sqrt (1 + γ)))) ∧
    ∀ f : ℝ →ᵇ ℝ,
      Tendsto (fun n : ℕ =>
          ∫ s, f (condFisherRejProb μ ⌊γ * (n : ℝ)⌋₊ α s) ∂(Measure.pi fun _ : Fin n => μ))
        atTop (𝓝 (∫ w, f (normSurv (quantile stdNormal (1 - α) + Real.sqrt γ * w)) ∂stdNormal)) := by sorry

end ConformalOutlierTesting
