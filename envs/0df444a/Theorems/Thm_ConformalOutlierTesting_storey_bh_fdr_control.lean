-- Prove2me | Theorems.Thm_ConformalOutlierTesting_storey_bh_fdr_control
-- name    : ConformalOutlierTesting.storey_bh_fdr_control
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:59:32.223614+00:00
-- url     : https://prove2.me/theorems/9d6c2c7b-2964-4bbf-a6ae-ca0715ea0bfe
-- title:
--   Theorem 3: Storey's BH with conformal p-values controls the FDR
-- statement:
--   Let $\lambda=K/(n+1)$ for an integer $K$ with $1\le K\le n$, so that $\lambda\in(0,1)$. Let the scores be continuously distributed, in the setting of Theorem 2 and Corollary 1. Then the BH procedure with Storey's correction, at level $\alpha\in(0,1)$, applied to the marginal conformal p-values controls the FDR at level $\alpha$:
--
--   $$\mathbb E\left[\frac{|\mathcal R\cap\mathcal H_0|}{\max\{1,|\mathcal R|\}}\right]\le\alpha.$$
--
--   So the positive dependence among conformal p-values does not break the FDR control of adaptive BH, although Storey's correction can fail for general PRDS p-values.
--
--   **Formalization Note** The paper says "for any integer $K$". The procedure needs $\lambda\in(0,1)$ (Appendix A.4), hence $1\le K\le n$. Storey's estimate uses $I(p_i\ge\lambda)$ as in Appendix A.4, where the procedure is defined. The main text writes $I(p_i>\lambda)$.
-- source:
--   Bates, Candès, Lei, Romano and Sesia, Testing for Outliers with Conformal p-values, arXiv:2104.08279v3 (2022), Section 2.3, Theorem 3, eq. (8), p. 8; procedure defined in Appendix A.4, p. 42; proof pp. 44-45

import Mathlib
import Definitions.Def_ConformalOutlierTesting_Basic

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction

namespace ConformalOutlierTesting

theorem storey_bh_fdr_control {n m : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (ν : Fin m → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)] (I : Finset (Fin m))
    (hI : ∀ j ∈ I, ν j = μ) (K : ℕ) (hK1 : 1 ≤ K) (hKn : K ≤ n)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    fdr (scoreLaw (n := n) μ ν) (fun ω => storeyRej α ((K : ℝ) / (n + 1)) (margPvals ω)) I ≤ α := by sorry

end ConformalOutlierTesting
