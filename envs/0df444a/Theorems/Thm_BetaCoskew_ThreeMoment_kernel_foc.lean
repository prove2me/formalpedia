-- Prove2me | Theorems.Thm_BetaCoskew_ThreeMoment_kernel_foc
-- name    : BetaCoskew.ThreeMoment.kernel_foc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:58.438649+00:00
-- url     : https://prove2.me/theorems/9d87455b-345e-4118-8dc3-75fb4449be91
-- title:
--   Appendix A, p. 34: first-order equilibrium pricing kernel
-- statement:
--   In the paper's atomless one-period market, assume the representative investor's rank-dependent utility satisfies Assumption 1, that the market return $\tilde R_M=\sum_i x_i^M R_i$ maximizes the feasible RDU problem (P′), and that its CDF $F_M$ is continuous. Then there is a positive multiplier $\lambda^*$ such that, almost surely,
--
--   $$
--   \tilde m=(\lambda^*)^{-1}w'(1-F_M(\tilde R_M))u'(\tilde R_M).
--   $$
--
--   This is the first-order form used in Appendix A to identify the equilibrium kernel. The risk-free pricing equation determines $\lambda^*$ in equation (12).
--
--   **Formalization Note** Equilibrium is optimization of the RDU objective over the eligible payoffs defined in the model; the kernel identity is a conclusion, not part of that definition.
-- source:
--   Shi, Cui & Zhou, Beta and coskewness pricing: perspective from probability weighting, SSRN 3579960 (version of June 2, 2020), pp. 33–34, Appendix A, first displayed formula (from Xia & Zhou 2016, Theorem 5.2)

import Mathlib
import Definitions.Def_BetaCoskew_ThreeMoment_Model

namespace BetaCoskew.ThreeMoment

open MeasureTheory ProbabilityTheory

/-- Appendix A, pp. 33–34: the first-order equilibrium pricing kernel. -/
theorem kernel_foc {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP : Atomless P)
    (u w : ℝ → ℝ) (hu : UtilityAssumption u) (hw : WeightingAssumption w)
    (rf : ℝ) (mt : Ω → ℝ) {n : ℕ} (R : Fin n → Ω → ℝ)
    (hmkt : IsPricedMarket P mt rf R)
    (xM : Fin n → ℝ) (hxM : ∑ i, xM i = 1)
    (hEq : IsEquilibrium P u w mt (fun ω => ∑ i, xM i * R i ω))
    (hF : Continuous (cdf (P.map (fun ω => ∑ i, xM i * R i ω)))) :
    let RM : Ω → ℝ := fun ω => ∑ i, xM i * R i ω
    ∃ lam : ℝ, 0 < lam ∧
      mt =ᵐ[P] fun ω => lam⁻¹ *
        (deriv w (1 - cdf (P.map RM) (RM ω)) * deriv u (RM ω)) := by sorry

end BetaCoskew.ThreeMoment
