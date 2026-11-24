-- Prove2me | Theorems.Thm_ConformalOutlierTesting_conformal_pvalues_prds
-- name    : ConformalOutlierTesting.conformal_pvalues_prds
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:58:12.791898+00:00
-- url     : https://prove2.me/theorems/8a32fce4-2a43-414e-9838-abeff0011ca7
-- title:
--   Theorem 2: conformal p-values are PRDS
-- statement:
--   Let the scores be continuously distributed with law $\mu$. Let $n$ calibration scores be i.i.d. with law $\mu$, and let $m$ test points have independent scores, independent of the calibration data. The scores of the inliers $j\in I$ have law $\mu$, and the scores of the outliers have arbitrary laws. Then the marginal conformal p-values
--
--   $$\big(\hat u^{(\mathrm{marg})}(X_{2n+1}),\dots,\hat u^{(\mathrm{marg})}(X_{2n+m})\big)$$
--
--   are PRDS on the set $I$ of inliers. That is, for every inlier $i$ and every increasing set $A$, $\mathbb P[(p_1,\dots,p_m)\in A\mid p_i=x]$ is nondecreasing in $x$.
--
--   Together with Benjamini and Yekutieli (2001), this shows that the BH procedure applied to conformal p-values controls the FDR.
--
--   **Formalization Note** The paper's wording asks only that "the inliers are jointly independent of each other and of the data in $\mathcal D$". The proof (Lemma 4, general case) assumes that all test points are mutually independent and independent of $\mathcal D$, as stated in Section 1.1, and the formal statement assumes the same. This is more than is needed. The outliers may depend on one another, as the paper notes in Section 6, but they must be independent of the inliers and of $\mathcal D$. Without that the conclusion can fail (see the mission report). Increasing sets are taken measurable. Since the p-values take finitely many values, this loses nothing. The conditional probability is a conditional expectation given $\sigma(p_i)$, and PRDS asks for a nondecreasing version of it.
-- source:
--   Bates, Candès, Lei, Romano and Sesia, Testing for Outliers with Conformal p-values, arXiv:2104.08279v3 (2022), Section 2.2, Theorem 2 and Definition 1, pp. 6-7; proof in Appendix A.3, pp. 39-40

import Mathlib
import Definitions.Def_ConformalOutlierTesting_Basic

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction

namespace ConformalOutlierTesting

theorem conformal_pvalues_prds {n m : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (ν : Fin m → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)] (I : Finset (Fin m))
    (hI : ∀ j ∈ I, ν j = μ) :
    IsPRDS (scoreLaw (n := n) μ ν) margPvals I := by sorry

end ConformalOutlierTesting
