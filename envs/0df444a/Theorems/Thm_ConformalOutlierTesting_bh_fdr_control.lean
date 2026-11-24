-- Prove2me | Theorems.Thm_ConformalOutlierTesting_bh_fdr_control
-- name    : ConformalOutlierTesting.bh_fdr_control
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:58:35.703172+00:00
-- url     : https://prove2.me/theorems/4685ea2e-2d7e-4821-ad09-574b9a1b6658
-- title:
--   Corollary 1: BH with conformal p-values controls the FDR at level π₀α
-- statement:
--   In the setting of Theorem 2, apply the BH procedure at level $\alpha\in(0,1)$ to the marginal conformal p-values $(\hat u^{(\mathrm{marg})}(X_{2n+1}),\dots,\hat u^{(\mathrm{marg})}(X_{2n+m}))$. Let $\mathcal H_0$ be the set of inliers and $\pi_0=|\mathcal H_0|/m$. Then
--
--   $$\mathbb E\left[\frac{|\mathcal R\cap\mathcal H_0|}{\max\{1,|\mathcal R|\}}\right]\le\pi_0\alpha\le\alpha,$$
--
--   where $\mathcal R$ is the set of test points reported as outliers.
--
--   The guarantee holds on average over the calibration data.
-- source:
--   Bates, Candès, Lei, Romano and Sesia, Testing for Outliers with Conformal p-values, arXiv:2104.08279v3 (2022), Section 2.2, Corollary 1, eq. (7), p. 7

import Mathlib
import Definitions.Def_ConformalOutlierTesting_Basic

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction

namespace ConformalOutlierTesting

theorem bh_fdr_control {n m : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (ν : Fin m → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)] (I : Finset (Fin m))
    (hI : ∀ j ∈ I, ν j = μ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    fdr (scoreLaw (n := n) μ ν) (fun ω => bhRej α (margPvals ω)) I ≤ (I.card : ℝ) / m * α ∧
      (I.card : ℝ) / m * α ≤ α := by sorry

end ConformalOutlierTesting
