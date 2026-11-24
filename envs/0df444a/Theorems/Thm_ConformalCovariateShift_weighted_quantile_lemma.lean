-- Prove2me | Theorems.Thm_ConformalCovariateShift_weighted_quantile_lemma
-- name    : ConformalCovariateShift.weighted_quantile_lemma
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T02:23:27.071665+00:00
-- url     : https://prove2.me/theorems/071a09a3-45c9-49ce-8eb7-ba98337d5de3
-- title:
--   Lemma 3: weighted quantile lemma
-- statement:
--   Let $Z_1,\dots,Z_{n+1}$ be weighted exchangeable random variables with values in a measurable space $E$, with weight functions $w_1,\dots,w_{n+1}$. Let $\mathcal S$ be a score function and $V_i=\mathcal S(Z_i,Z_{-i})$, where $Z_{-i}=Z_{1:(n+1)}\setminus\{Z_i\}$, for $i=1,\dots,n+1$. Define
--
--   $$p_i^w(z_1,\dots,z_{n+1})=\frac{\sum_{\sigma:\sigma(n+1)=i}\prod_{j=1}^{n+1}w_j(z_{\sigma(j)})}{\sum_\sigma\prod_{j=1}^{n+1}w_j(z_{\sigma(j)})},\qquad i=1,\dots,n+1,$$
--
--   the sums running over permutations $\sigma$ of $1,\dots,n+1$. Then for every $\beta\in(0,1)$,
--
--   $$\mathbb{P}\bigg\{V_{n+1}\le\mathrm{Quantile}\bigg(\beta;\sum_{i=1}^np_i^w(Z_1,\dots,Z_{n+1})\delta_{V_i}+p_{n+1}^w(Z_1,\dots,Z_{n+1})\delta_\infty\bigg)\bigg\}\ge\beta.$$
--
--   This is the weighted generalization of Lemma 1, and the main technical result of the paper.
--
--   **Formalization Note** The score function is assumed measurable as in Theorem 1. In weighted exchangeability the base measure is required to be invariant under permutations of the coordinates; with an arbitrary base measure, as in the paper's footnote, the lemma is false.
-- source:
--   Tibshirani, Barber, Candès and Ramdas, Conformal Prediction Under Covariate Shift, arXiv:1904.06019v3 (2019), Section 3.3, Lemma 3, eq. (15), p. 12

import Mathlib
import Definitions.Def_ConformalCovariateShift_Basic

open MeasureTheory ProbabilityTheory

namespace ConformalCovariateShift

theorem weighted_quantile_lemma {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P] {n : ℕ} (Z : Fin (n + 1) → Omega → E)
    (w : Fin (n + 1) → E → ℝ) (hZ : IsWeightedExchangeable P Z w)
    (S : ScoreFn E) (hS : ∀ i, Measurable (fun z : Fin (n + 1) → E => scores S z i))
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ENNReal.ofReal β ≤
      P {ω | (scores S (fun k => Z k ω) (Fin.last n) : EReal) ≤
        quantile β (augDist (permWeight w (fun k => Z k ω)) (scores S (fun k => Z k ω)))} := by sorry

end ConformalCovariateShift
