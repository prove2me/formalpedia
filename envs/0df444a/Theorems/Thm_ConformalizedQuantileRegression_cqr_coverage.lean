-- Prove2me | Theorems.Thm_ConformalizedQuantileRegression_cqr_coverage
-- name    : ConformalizedQuantileRegression.cqr_coverage
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:44:34.617288+00:00
-- url     : https://prove2.me/theorems/3f173e6d-ad84-4350-a0e1-102ed481bc6c
-- title:
--   Theorem 1: validity of split conformalized quantile regression
-- statement:
--   Let $(X_i,Y_i)\in\mathbb{R}^p\times\mathbb{R}$, $i=1,\dots,n+1$, be exchangeable. Partition $\{1,\dots,n\}$ into disjoint sets $\mathcal I_1,\mathcal I_2$ with $\mathcal I_1\cup\mathcal I_2=\{1,\dots,n\}$ and $\mathcal I_2\neq\emptyset$, and let $\alpha\in(0,1)$. Fit $\hat q_{\mathrm{lo}},\hat q_{\mathrm{hi}}$ with a measurable quantile regression algorithm $\mathcal A$ on the proper training set $\{(X_i,Y_i):i\in\mathcal I_1\}$, compute the conformity scores $E_i=\max\{\hat q_{\mathrm{lo}}(X_i)-Y_i,\,Y_i-\hat q_{\mathrm{hi}}(X_i)\}$ for $i\in\mathcal I_2$, let $Q_{1-\alpha}(E,\mathcal I_2)$ be their $(1-\alpha)(1+1/|\mathcal I_2|)$-th empirical quantile, and let
--
--   $$C(x)=\big[\hat q_{\mathrm{lo}}(x)-Q_{1-\alpha}(E,\mathcal I_2),\ \hat q_{\mathrm{hi}}(x)+Q_{1-\alpha}(E,\mathcal I_2)\big].$$
--
--   Then
--
--   $$\mathbb{P}\{Y_{n+1}\in C(X_{n+1})\}\ge1-\alpha.$$
--
--   If moreover the conformity scores $E_i$, $i\in\mathcal I_2\cup\{n+1\}$, are almost surely distinct, then
--
--   $$\mathbb{P}\{Y_{n+1}\in C(X_{n+1})\}\le1-\alpha+\frac{1}{|\mathcal I_2|+1}.$$
--
--   The guarantee holds for every joint distribution of the data and every quantile regression algorithm, however inaccurate.
--
--   **Formalization Note** The split is fixed (deterministic); a random split drawn independently of the data is covered by conditioning on it. The fitted functions are required to depend measurably on the training data and the input, the standing convention that makes the coverage event measurable. $Q_{1-\alpha}(E,\mathcal I_2)$ is valued in the extended reals; when $(1-\alpha)(1+1/|\mathcal I_2|)>1$ it is $+\infty$ and $C(x)=\mathbb{R}$. The distinctness hypothesis is read as distinctness of the calibration and test scores.
-- source:
--   Romano, Patterson and Candès, Conformalized Quantile Regression, arXiv:1905.03222v1 (2019), Section 4, Theorem 1 and Algorithm 1, eqs. (9)-(11), pp. 5-6

import Mathlib
import Definitions.Def_ConformalizedQuantileRegression_Basic

open MeasureTheory ProbabilityTheory

namespace ConformalizedQuantileRegression

theorem cqr_coverage {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {p n : ℕ} (Z : Fin (n + 1) → Ω → Sample p) (hZ : IsExchangeable P Z)
    (I₁ I₂ : Finset (Fin n)) (hdisj : Disjoint I₁ I₂) (hsplit : I₁ ∪ I₂ = Finset.univ)
    (hI₂ : I₂.Nonempty) (A : QRAlgorithm p I₁) (hA : IsMeasurableAlgorithm A)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ENNReal.ofReal (1 - α) ≤
        P {ω | (Z (Fin.last n) ω).2 ∈
          cqrInterval A I₂ α (fun i => Z i.castSucc ω) (Z (Fin.last n) ω).1} ∧
    ((∀ᵐ ω ∂P, Set.InjOn
        (fun j => conformityScore (fitQR A (fun i => Z i.castSucc ω)).1
          (fitQR A (fun i => Z i.castSucc ω)).2 (Z j ω))
        (↑(I₂.map Fin.castSuccEmb ∪ {Fin.last n}) : Set (Fin (n + 1)))) →
      P {ω | (Z (Fin.last n) ω).2 ∈
          cqrInterval A I₂ α (fun i => Z i.castSucc ω) (Z (Fin.last n) ω).1} ≤
        ENNReal.ofReal (1 - α + 1 / ((I₂.card : ℝ) + 1))) := by sorry

end ConformalizedQuantileRegression
