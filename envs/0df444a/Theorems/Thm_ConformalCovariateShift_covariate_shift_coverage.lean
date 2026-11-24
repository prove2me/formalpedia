-- Prove2me | Theorems.Thm_ConformalCovariateShift_covariate_shift_coverage
-- name    : ConformalCovariateShift.covariate_shift_coverage
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T02:24:59.644668+00:00
-- url     : https://prove2.me/theorems/73b6ee2e-b210-468b-a6f7-4a07fc5bc063
-- title:
--   Corollary 1: coverage of weighted conformal prediction under covariate shift
-- statement:
--   Assume the covariate-shift model (6): $(X_i,Y_i)$, $i=1,\dots,n$, are i.i.d. from $P=P_X\times P_{Y|X}$, and $(X_{n+1},Y_{n+1})\sim\widetilde P=\widetilde P_X\times P_{Y|X}$ independently, where $P_X,\widetilde P_X$ are probability measures on $\mathbb{R}^d$ and $P_{Y|X}$ is a common conditional law. Assume $\widetilde P_X$ is absolutely continuous with respect to $P_X$, and let $w=d\widetilde P_X/dP_X$. For a score function $\mathcal S$ and $\alpha\in(0,1)$ define
--
--   $$\widehat C_n(x)=\bigg\{y\in\mathbb{R}:V_{n+1}^{(x,y)}\le\mathrm{Quantile}\bigg(1-\alpha;\sum_{i=1}^np_i^w(x)\delta_{V_i^{(x,y)}}+p_{n+1}^w(x)\delta_\infty\bigg)\bigg\},$$
--
--   with the scores (4) and the weights $p_i^w(x)=w(X_i)/(\sum_{j=1}^nw(X_j)+w(x))$, $p_{n+1}^w(x)=w(x)/(\sum_{j=1}^nw(X_j)+w(x))$ of (7). Then
--
--   $$\mathbb{P}\big\{Y_{n+1}\in\widehat C_n(X_{n+1})\big\}\ge1-\alpha.$$
--
--   This is the paper's main result: weighting the nonconformity scores by the likelihood ratio of test to training covariates restores the coverage guarantee of conformal prediction under covariate shift.
--
--   **Formalization Note** The conditional law $P_{Y|X}$ is a Markov kernel $K$ and the joint laws are $P_X\otimes K$ and $\widetilde P_X\otimes K$. The likelihood ratio is any measurable, nonnegative, real-valued version of $d\widetilde P_X/dP_X$, i.e. a function equal $P_X$-almost everywhere to Mathlib's `rnDeriv`. The score function is assumed measurable as in Theorem 1.
-- source:
--   Tibshirani, Barber, Candès and Ramdas, Conformal Prediction Under Covariate Shift, arXiv:1904.06019v3 (2019), Section 2.1, Corollary 1, eqs. (6)-(8), p. 4; proof in Section 3.5, p. 14

import Mathlib
import Definitions.Def_ConformalCovariateShift_Basic

open MeasureTheory ProbabilityTheory

namespace ConformalCovariateShift

theorem covariate_shift_coverage {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P] {d n : ℕ}
    (PX PXt : Measure (Fin d → ℝ)) [IsProbabilityMeasure PX] [IsProbabilityMeasure PXt]
    (K : Kernel (Fin d → ℝ) ℝ) [IsMarkovKernel K]
    (Z : Fin (n + 1) → Omega → DataPt d) (hZm : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (htrain : ∀ i : Fin n, Measure.map (Z i.castSucc) P = PX ⊗ₘ K)
    (htest : Measure.map (Z (Fin.last n)) P = PXt ⊗ₘ K)
    (hac : PXt ≪ PX) (w : (Fin d → ℝ) → ℝ) (hw_meas : Measurable w) (hw_nonneg : ∀ x, 0 ≤ w x)
    (hw : ∀ᵐ x ∂PX, ENNReal.ofReal (w x) = PXt.rnDeriv PX x)
    (S : ScoreFn (DataPt d)) (hS : ∀ i, Measurable (fun z : Fin (n + 1) → DataPt d => scores S z i))
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ENNReal.ofReal (1 - α) ≤
      P {ω | (Z (Fin.last n) ω).2 ∈
        covShiftBand S α w (fun i => Z i.castSucc ω) (Z (Fin.last n) ω).1} := by sorry

end ConformalCovariateShift
