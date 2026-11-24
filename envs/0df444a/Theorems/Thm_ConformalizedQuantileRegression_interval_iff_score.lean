-- Prove2me | Theorems.Thm_ConformalizedQuantileRegression_interval_iff_score
-- name    : ConformalizedQuantileRegression.interval_iff_score
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:42:51.517805+00:00
-- url     : https://prove2.me/theorems/3f7b3c24-875a-4378-9ae8-ff7cd631a539
-- title:
--   Theorem 1 (proof): $Y\in C(X)$ iff $E\le Q_{1-\alpha}(E,\mathcal I_2)$
-- statement:
--   Let $\hat q_{\mathrm{lo}},\hat q_{\mathrm{hi}}$ be the quantile functions that a quantile regression algorithm fits on the proper training set, let $Q_{1-\alpha}(E,\mathcal I_2)$ be the $(1-\alpha)(1+1/|\mathcal I_2|)$-th empirical quantile of the calibration scores, and let $C$ be the CQR interval (10). For every sample $(x,y)\in\mathbb{R}^p\times\mathbb{R}$, with conformity score $E=\max\{\hat q_{\mathrm{lo}}(x)-y,\;y-\hat q_{\mathrm{hi}}(x)\}$,
--
--   $$y\in C(x)\quad\Longleftrightarrow\quad E\le Q_{1-\alpha}(E,\mathcal I_2).$$
--
--   This converts coverage of the test response into a comparison of the test score with an empirical quantile of the calibration scores.
--
--   **Formalization Note** The statement holds for every level $\alpha$ and every split, as in the paper ("by the construction of the prediction interval"); $Q_{1-\alpha}(E,\mathcal I_2)$ is valued in the extended reals.
-- source:
--   Romano, Patterson and Candès, Conformalized Quantile Regression, arXiv:1905.03222v1 (2019), Section 4, proof of Theorem 1, display before eq. (12), p. 6

import Mathlib
import Definitions.Def_ConformalizedQuantileRegression_Basic

open MeasureTheory ProbabilityTheory

namespace ConformalizedQuantileRegression

theorem interval_iff_score {p n : ℕ} {I₁ : Finset (Fin n)} (A : QRAlgorithm p I₁)
    (I₂ : Finset (Fin n)) (α : ℝ) (d : Fin n → Sample p) (z : Sample p) :
    z.2 ∈ cqrInterval A I₂ α d z.1 ↔
      (conformityScore (fitQR A d).1 (fitQR A d).2 z : EReal) ≤ cqrCorrection A I₂ α d := by sorry

end ConformalizedQuantileRegression
