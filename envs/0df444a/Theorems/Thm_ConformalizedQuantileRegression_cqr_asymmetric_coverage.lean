-- Prove2me | Theorems.Thm_ConformalizedQuantileRegression_cqr_asymmetric_coverage
-- name    : ConformalizedQuantileRegression.cqr_asymmetric_coverage
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:45:07.380574+00:00
-- url     : https://prove2.me/theorems/b42425ba-f892-426c-8b94-6161004a36c0
-- title:
--   Theorem 2 (as proved): asymmetric conformalization controls each tail
-- statement:
--   Let $(X_i,Y_i)\in\mathbb{R}^p\times\mathbb{R}$, $i=1,\dots,n+1$, be exchangeable. Partition $\{1,\dots,n\}$ into disjoint sets $\mathcal I_1,\mathcal I_2$ with $\mathcal I_1\cup\mathcal I_2=\{1,\dots,n\}$ and $\mathcal I_2\neq\emptyset$ and fit $\hat q_{\mathrm{lo}},\hat q_{\mathrm{hi}}$ with a measurable quantile regression algorithm on $\{(X_i,Y_i):i\in\mathcal I_1\}$. Let $\alpha_{\mathrm{lo}},\alpha_{\mathrm{hi}}\in(0,1)$. Let $Q_{\mathrm{lo}}$ be the $(1-\alpha_{\mathrm{lo}})(1+1/|\mathcal I_2|)$-th empirical quantile of $\{\hat q_{\mathrm{lo}}(X_i)-Y_i:i\in\mathcal I_2\}$ and $Q_{\mathrm{hi}}$ the $(1-\alpha_{\mathrm{hi}})(1+1/|\mathcal I_2|)$-th empirical quantile of $\{Y_i-\hat q_{\mathrm{hi}}(X_i):i\in\mathcal I_2\}$, and let $C(x)=[\hat q_{\mathrm{lo}}(x)-Q_{\mathrm{lo}},\ \hat q_{\mathrm{hi}}(x)+Q_{\mathrm{hi}}]$. Then
--
--   1. $\mathbb{P}\{Y_{n+1}\ge\hat q_{\mathrm{lo}}(X_{n+1})-Q_{\mathrm{lo}}\}\ge1-\alpha_{\mathrm{lo}}$;
--   2. $\mathbb{P}\{Y_{n+1}\le\hat q_{\mathrm{hi}}(X_{n+1})+Q_{\mathrm{hi}}\}\ge1-\alpha_{\mathrm{hi}}$;
--   3. consequently, with $\alpha=\alpha_{\mathrm{lo}}+\alpha_{\mathrm{hi}}$,
--
--   $$\mathbb{P}\{Y_{n+1}\in C(X_{n+1})\}\ge1-\alpha.$$
--
--   Controlling the two tails separately gives a stronger guarantee than Theorem 1, at the price of slightly longer intervals.
--
--   **Formalization Note** This is Theorem 2 as its proof establishes it. The paper prints the uninflated levels $1-\alpha_{\mathrm{lo}}$ and $1-\alpha_{\mathrm{hi}}$, for which the claim is false (with $|\mathcal I_2|=2$, $\hat q_{\mathrm{lo}}=\hat q_{\mathrm{hi}}=0$, i.i.d. standard normal responses and $\alpha_{\mathrm{lo}}=\alpha_{\mathrm{hi}}=1/4$, the three probabilities are $2/3,2/3,1/3$ instead of at least $3/4,3/4,1/2$); its proof applies Lemma 2, which requires the inflated levels used here. In the paper $\alpha_{\mathrm{lo}},\alpha_{\mathrm{hi}}$ in Theorem 2 are the two tail miscoverage rates (not the quantile levels $\alpha/2$, $1-\alpha/2$ of Section 2), and the range $(0,1)$ is the range of Lemma 2. The split is fixed and the empirical quantiles are valued in the extended reals.
-- source:
--   Romano, Patterson and Candès, Conformalized Quantile Regression, arXiv:1905.03222v1 (2019), Section 4, Theorem 2, eqs. (15)-(16), p. 7; empirical quantiles at the inflated levels (1 - α_lo)(1 + 1/|I₂|) and (1 - α_hi)(1 + 1/|I₂|) used by the proof via Lemma 2 (printed: 1 - α_lo and 1 - α_hi)

import Mathlib
import Definitions.Def_ConformalizedQuantileRegression_Basic

open MeasureTheory ProbabilityTheory

namespace ConformalizedQuantileRegression

theorem cqr_asymmetric_coverage {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {p n : ℕ} (Z : Fin (n + 1) → Ω → Sample p) (hZ : IsExchangeable P Z)
    (I₁ I₂ : Finset (Fin n)) (hdisj : Disjoint I₁ I₂) (hsplit : I₁ ∪ I₂ = Finset.univ)
    (hI₂ : I₂.Nonempty) (A : QRAlgorithm p I₁) (hA : IsMeasurableAlgorithm A)
    (αlo αhi : ℝ) (hlo0 : 0 < αlo) (hlo1 : αlo < 1) (hhi0 : 0 < αhi) (hhi1 : αhi < 1) :
    ENNReal.ofReal (1 - αlo) ≤
        P {ω | ((fitQR A (fun i => Z i.castSucc ω)).1 (Z (Fin.last n) ω).1 : EReal) -
            loCorrection A I₂ ((1 - αlo) * (1 + 1 / (I₂.card : ℝ))) (fun i => Z i.castSucc ω) ≤
          ((Z (Fin.last n) ω).2 : EReal)} ∧
    ENNReal.ofReal (1 - αhi) ≤
        P {ω | ((Z (Fin.last n) ω).2 : EReal) ≤
          ((fitQR A (fun i => Z i.castSucc ω)).2 (Z (Fin.last n) ω).1 : EReal) +
            hiCorrection A I₂ ((1 - αhi) * (1 + 1 / (I₂.card : ℝ))) (fun i => Z i.castSucc ω)} ∧
    ENNReal.ofReal (1 - (αlo + αhi)) ≤
        P {ω | (Z (Fin.last n) ω).2 ∈
          asymInterval A I₂ ((1 - αlo) * (1 + 1 / (I₂.card : ℝ)))
            ((1 - αhi) * (1 + 1 / (I₂.card : ℝ))) (fun i => Z i.castSucc ω) (Z (Fin.last n) ω).1} := by sorry

end ConformalizedQuantileRegression
