-- Prove2me | Theorems.Thm_ConformalOutlierTesting_fpr_beta_distribution
-- name    : ConformalOutlierTesting.fpr_beta_distribution
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T08:00:07.573496+00:00
-- url     : https://prove2.me/theorems/59ab3d6c-800f-43b5-a762-0a7db7736626
-- title:
--   Proposition 1: the pointwise FPR has a Beta distribution
-- statement:
--   Let the scores be continuously distributed with law $\mu$, and let the $n$ calibration scores be i.i.d. with law $\mu$. Let $\alpha<1$ with $\ell=\lfloor(n+1)\alpha\rfloor\ge1$. Then the conditional false positive rate
--
--   $$\mathrm{FPR}(\alpha;\mathcal D)=\mathbb P\big[\hat u^{(\mathrm{marg})}(X_{2n+1})\le\alpha\mid\mathcal D\big]$$
--
--   follows the $\mathrm{Beta}(\ell,\,n+1-\ell)$ distribution.
--
--   Its mean is $\ell/(n+1)\le\alpha$, but it exceeds $\alpha$ with non-negligible probability.
--
--   **Formalization Note** The paper does not restrict $\alpha$. For $\alpha<1/(n+1)$ one has $\ell=0$, and $\mathrm{Beta}(0,n+1)$ is not a distribution (the FPR is then $0$). For $\alpha\ge1$ the second parameter is not positive. The hypotheses $\ell\ge1$ and $\alpha<1$ exclude these cases.
-- source:
--   Bates, Candès, Lei, Romano and Sesia, Testing for Outliers with Conformal p-values, arXiv:2104.08279v3 (2022), Section 3.1, Proposition 1, eq. (9), p. 8

import Mathlib
import Definitions.Def_ConformalOutlierTesting_Basic

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction

namespace ConformalOutlierTesting

theorem fpr_beta_distribution {n : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (α : ℝ) (hα1 : α < 1) (hl : 1 ≤ ⌊((n : ℝ) + 1) * α⌋₊) :
    (Measure.pi fun _ : Fin n => μ).map (fun s => fpr μ s α) =
      betaMeasure (⌊((n : ℝ) + 1) * α⌋₊ : ℝ) ((n : ℝ) + 1 - ⌊((n : ℝ) + 1) * α⌋₊) := by sorry

end ConformalOutlierTesting
