-- Prove2me | Theorems.Thm_ConformalCovariateShift_weighted_conformal_coverage
-- name    : ConformalCovariateShift.weighted_conformal_coverage
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T02:23:56.601411+00:00
-- url     : https://prove2.me/theorems/83a1a698-92f5-439c-8e2b-a90cc4c12f5c
-- title:
--   Theorem 2: coverage of weighted conformal prediction
-- statement:
--   Let $Z_i=(X_i,Y_i)\in\mathbb{R}^d\times\mathbb{R}$, $i=1,\dots,n+1$, be weighted exchangeable with weight functions $w_1,\dots,w_{n+1}$. Let $\mathcal S$ be a score function and $\alpha\in(0,1)$, and define the weighted conformal band at $x\in\mathbb{R}^d$ by
--
--   $$\widehat C_n(x)=\bigg\{y\in\mathbb{R}:V_{n+1}^{(x,y)}\le\mathrm{Quantile}\bigg(1-\alpha;\sum_{i=1}^np_i^w\big(Z_1,\dots,Z_n,(x,y)\big)\delta_{V_i^{(x,y)}}+p_{n+1}^w\big(Z_1,\dots,Z_n,(x,y)\big)\delta_\infty\bigg)\bigg\},$$
--
--   with the scores (4) and the weights (15). Then
--
--   $$\mathbb{P}\big\{Y_{n+1}\in\widehat C_n(X_{n+1})\big\}\ge1-\alpha.$$
--
--   This extends conformal prediction from exchangeable to weighted exchangeable data.
--
--   **Formalization Note** The score function is assumed measurable as in Theorem 1, and weighted exchangeability is that of the definitions file (permutation-invariant base measure).
-- source:
--   Tibshirani, Barber, Candès and Ramdas, Conformal Prediction Under Covariate Shift, arXiv:1904.06019v3 (2019), Section 3.4, Theorem 2, eq. (16), p. 13

import Mathlib
import Definitions.Def_ConformalCovariateShift_Basic

open MeasureTheory ProbabilityTheory

namespace ConformalCovariateShift

theorem weighted_conformal_coverage {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P] {d n : ℕ} (Z : Fin (n + 1) → Omega → DataPt d)
    (w : Fin (n + 1) → DataPt d → ℝ) (hZ : IsWeightedExchangeable P Z w)
    (S : ScoreFn (DataPt d)) (hS : ∀ i, Measurable (fun z : Fin (n + 1) → DataPt d => scores S z i))
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ENNReal.ofReal (1 - α) ≤
      P {ω | (Z (Fin.last n) ω).2 ∈
        weightedConformalBand S α w (fun i => Z i.castSucc ω) (Z (Fin.last n) ω).1} := by sorry

end ConformalCovariateShift
