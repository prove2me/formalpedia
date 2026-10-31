-- Prove2me | Theorems.Thm_DistributionFreeInventory_TwoLocation_theorem_1
-- name    : DistributionFreeInventory.TwoLocation.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:30:50.421332+00:00
-- url     : https://prove2.me/theorems/71a3c1cb-6aff-43f0-9f74-d97ba3e62c7d
-- title:
--   Theorem 1 — two-location worst-case cost and attainment
-- statement:
--   Let two locations have arbitrary real means $m_i$, nonnegative standard deviations $\sigma_i$, and covariance parameter $-1\le\rho\le1$. Let $h,p,s_0>0$ and $p+h>s>s_0$, with local shipment cost $s_0$ and cross-location cost $s$. For every inventory pair $y\in\mathbb R^2$, the printed claim is
--   $$\sup_{f\in\mathcal F}\mathbb E_f[C(y,d)]\le s_0(m_1+m_2)-\tfrac12(p-h-s_0)(y_1+y_2-m_1-m_2)
--    +(p+h-s_0)\Phi\!\left(y;\frac{3(p+h-s)+s-s_0}{p+h-s_0}\right).$$
--   Moreover, if Condition 1 holds with $\zeta=(p+h-s)/(s-s_0)$, some law $f^*\in\mathcal F$ with at most six support points has expected cost equal to the right side. Thus the asserted upper bound is attained under that condition.
--
--   Here $C$ remains the literal nonnegative-flow optimum of equation (2), including positive infinity on infeasible demand realizations, and $\mathcal F$ includes all Borel laws on the real plane with the specified finite second moments. This preserves the source-domain issue recorded in INSIGHTS.yaml: the printed inequality is contradicted by a valid law giving negative demands positive probability. No positivity-of-demand or recourse-finiteness hypothesis has been added.
--
--   Differences from the source:
--   - encoding: coordinates numbered 1 and 2 on the real plane → zero-based Fin 2 coordinates on EuclideanSpace ℝ (Fin 2); reason: the canonical coordinate identification preserves every vector and Borel law
--   - encoding: prescribed first and raw second moments → published MeanCovClass with MemLp 2, means and central covariance; reason: for probability laws with finite second moments these are equivalent moment equations and exclude default integrals
--   - generalization: correlation coefficient of two demands → nonnegative standard deviations including zero, with rho a covariance parameter in degenerate cases; reason: every source law with defined correlation is included, and zero-variance moment laws are also covered
--   - reading: six support points in the result and at most six on pages 4 and 16 → six nonnegative weights summing to one with possible zero weights or coincident atoms; reason: this retains the stated at-most-six support and actual attainment, including boundary probabilities
--   - encoding: Condition 1 uses quotients by Phi and nu-dependent denominators → conditionOne explicitly requires positive zeta and Phi only in the attainment antecedent; reason: these are the displayed condition’s well-definedness domain; no such restriction is imposed on the unconditional bound
--   - encoding: optimal recourse cost and its expectation → nonnegative extended infimum and integral, embedded in EReal and compared with an untruncated real bound; reason: infeasible recourse has value positive infinity; all feasible costs under the stated positivity assumptions are nonnegative
-- source:
--   Govindarajan, Sinha & Uichanco, Distribution-Free Inventory Risk Pooling in a Multilocation Newsvendor, DOI 10.1287/mnsc.2020.3719, held source.pdf, Theorem 1, equation (10), printed p. 15 (PDF 15); proof EC.2.5, ec11 (PDF 44)

import Definitions.Def_DistributionFreeInventory_TwoLocation_Bounds

namespace DistributionFreeInventory.TwoLocation

theorem theorem_1 (M : Moments) (h p s0 s : ℝ)
    (hh : 0 < h) (hp : 0 < p) (hs0 : 0 < s0) (hs : s0 < s) (hph : s < p+h)
    (y : Demand) :
    worstCost M h p s0 s y ≤ (costBound M h p s0 s y : EReal) ∧
    (conditionOne M y ((p+h-s)/(s-s0)) →
      ∃ μ ∈ ambiguity M, SixPointLaw μ ∧
        expectedCost h p s0 s y μ = (costBound M h p s0 s y : EReal)) := by sorry

end DistributionFreeInventory.TwoLocation
