-- Prove2me | Theorems.Thm_DistributionFreeInventory_TwoLocation_proposition_1
-- name    : DistributionFreeInventory.TwoLocation.proposition_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:30:59.408739+00:00
-- url     : https://prove2.me/theorems/8576575b-9c43-4d86-a085-f331cdfeaeca
-- title:
--   Proposition 1 — bivariate shortage bound and attainment
-- statement:
--   For any means $m_1,m_2\in\mathbb R$, standard deviations $\sigma_i\ge0$, covariance parameter $\rho\in[-1,1]$, $\zeta>0$, and inventory $y\in\mathbb R^2$, every Borel probability law $f\in\mathcal F$ with the specified finite second moments satisfies
--   $$\mathbb E_f[(d_1-y_1)^++(d_2-y_2)^++\zeta(d_1+d_2-y_1-y_2)^+]
--   \le\tfrac12(\zeta+1)(m_1-y_1+m_2-y_2)+(\zeta+1)\Phi\!\left(y;\frac{3\zeta+1}{\zeta+1}\right).$$
--   Moreover, if Condition 1 holds for these same data, some law $f^*\in\mathcal F$ supported on at most six points attains equality. The ambiguity set itself contains all moment laws, not just atomic laws. The shortage integrand is genuinely integrable by the finite second moment condition.
--
--   Differences from the source:
--   - encoding: coordinates numbered 1 and 2 on the real plane → zero-based Fin 2 coordinates on EuclideanSpace ℝ (Fin 2); reason: the canonical coordinate identification preserves every vector and Borel law
--   - encoding: prescribed first and raw second moments → published MeanCovClass with MemLp 2, means and central covariance; reason: for probability laws with finite second moments these are equivalent moment equations and exclude default integrals
--   - generalization: correlation coefficient of two demands → nonnegative standard deviations including zero, with rho a covariance parameter in degenerate cases; reason: every source law with defined correlation is included, and zero-variance moment laws are also covered
--   - reading: six support points in the result and at most six on pages 4 and 16 → six nonnegative weights summing to one with possible zero weights or coincident atoms; reason: this retains the stated at-most-six support and actual attainment, including boundary probabilities
--   - encoding: Condition 1 uses quotients by Phi and nu-dependent denominators → conditionOne explicitly requires positive zeta and Phi only in the attainment antecedent; reason: these are the displayed condition’s well-definedness domain; no such restriction is imposed on the unconditional bound
-- source:
--   Govindarajan, Sinha & Uichanco, Distribution-Free Inventory Risk Pooling in a Multilocation Newsvendor, DOI 10.1287/mnsc.2020.3719, held source.pdf, Proposition 1, equation (9), printed p. 15 (PDF 15); proof EC.2.3, ec5–ec9 (PDF 38–42)

import Definitions.Def_DistributionFreeInventory_TwoLocation_Bounds
open MeasureTheory

namespace DistributionFreeInventory.TwoLocation

theorem proposition_1 (M : Moments) (zeta : ℝ) (hzeta : 0 < zeta) (y : Demand) :
    (∀ μ ∈ ambiguity M, (∫ d, shortage zeta y d ∂μ) ≤ shortageBound M y zeta) ∧
    (conditionOne M y zeta → ∃ μ ∈ ambiguity M, SixPointLaw μ ∧
      (∫ d, shortage zeta y d ∂μ) = shortageBound M y zeta) := by sorry

end DistributionFreeInventory.TwoLocation
