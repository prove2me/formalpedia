-- Prove2me | Theorems.Thm_ConformalCovariateShift_conformal_coverage
-- name    : ConformalCovariateShift.conformal_coverage
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T02:22:38.910409+00:00
-- url     : https://prove2.me/theorems/38a64456-af39-4063-8084-9523f106d25d
-- title:
--   Theorem 1: coverage of conformal prediction
-- statement:
--   Let $Z_i=(X_i,Y_i)\in\mathbb{R}^d\times\mathbb{R}$, $i=1,\dots,n+1$, be exchangeable random variables, let $\mathcal S$ be a score function and let $\alpha\in(0,1)$. Let $\widehat C_n$ be the conformal band (5) built from $Z_1,\dots,Z_n$:
--
--   $$\widehat C_n(x)=\Big\{y\in\mathbb{R}:V_{n+1}^{(x,y)}\le\mathrm{Quantile}\big(1-\alpha;V_{1:n}^{(x,y)}\cup\{\infty\}\big)\Big\},$$
--
--   with the scores (4). Then
--
--   $$\mathbb{P}\big\{Y_{n+1}\in\widehat C_n(X_{n+1})\big\}\ge1-\alpha.$$
--
--   If moreover ties among $V_1^{(X_{n+1},Y_{n+1})},\dots,V_{n+1}^{(X_{n+1},Y_{n+1})}$ occur with probability zero, this probability is at most $1-\alpha+1/(n+1)$.
--
--   This is the finite-sample, distribution-free coverage guarantee of conformal prediction (Vovk et al. 2005; Lei et al. 2018).
--
--   **Formalization Note** The score function is assumed measurable in the sense that each map $(z_1,\dots,z_{n+1})\mapsto\mathcal S(z_i,z_{1:(n+1)}\setminus\{z_i\})$ is measurable, so that the scores are random variables; the paper uses this implicitly when it applies Lemma 1 to them. $\mathbb{R}^d$ is written as functions $\{1,\dots,d\}\to\mathbb{R}$.
-- source:
--   Tibshirani, Barber, Candès and Ramdas, Conformal Prediction Under Covariate Shift, arXiv:1904.06019v3 (2019), Section 1.2, Theorem 1, eqs. (4)-(5), p. 3

import Mathlib
import Definitions.Def_ConformalCovariateShift_Basic

open MeasureTheory ProbabilityTheory

namespace ConformalCovariateShift

theorem conformal_coverage {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    {d n : ℕ} (Z : Fin (n + 1) → Omega → DataPt d) (hZ : IsExchangeable P Z)
    (S : ScoreFn (DataPt d)) (hS : ∀ i, Measurable (fun z : Fin (n + 1) → DataPt d => scores S z i))
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ENNReal.ofReal (1 - α) ≤
      P {ω | (Z (Fin.last n) ω).2 ∈
        conformalBand S α (fun i => Z i.castSucc ω) (Z (Fin.last n) ω).1} ∧
    (P {ω | ∃ i j, i ≠ j ∧ scores S (fun k => Z k ω) i = scores S (fun k => Z k ω) j} = 0 →
      P {ω | (Z (Fin.last n) ω).2 ∈
        conformalBand S α (fun i => Z i.castSucc ω) (Z (Fin.last n) ω).1} ≤
        ENNReal.ofReal (1 - α + 1 / ((n : ℝ) + 1))) := by sorry

end ConformalCovariateShift
