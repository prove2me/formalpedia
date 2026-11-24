-- Prove2me | Theorems.Thm_ConformalizedQuantileRegression_quantile_inflation
-- name    : ConformalizedQuantileRegression.quantile_inflation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:41:56.513503+00:00
-- url     : https://prove2.me/theorems/a4553694-8bd5-4fe0-9e22-29da3172f8c3
-- title:
--   Lemma 2 (as proved): inflation of quantiles
-- statement:
--   Let $n\ge1$ and let $Z_1,\dots,Z_{n+1}$ be exchangeable real random variables. Let $\hat Q_n$ be the empirical quantile function of $Z_1,\dots,Z_n$. For every $\alpha\in(0,1)$,
--
--   $$\mathbb{P}\{Z_{n+1}\le\hat Q_n((1+\tfrac1n)\alpha)\}\ge\alpha.$$
--
--   If moreover $Z_1,\dots,Z_{n+1}$ are almost surely distinct, then also
--
--   $$\mathbb{P}\{Z_{n+1}\le\hat Q_n((1+\tfrac1n)\alpha)\}\le\alpha+\frac{1}{n+1}.$$
--
--   The inflated level $(1+\frac1n)\alpha$ accounts for the unseen $(n+1)$-st variable; this lemma is what the coverage theorems apply to the conformity scores.
--
--   **Formalization Note** This is Lemma 2 as its proof establishes it. The printed upper bound is $\alpha+\frac1n$; the proof (apply Lemma 1 with $n+1$ variables) gives the sharper $\alpha+\frac1{n+1}$, and the proof of Theorem 1 uses this sharper form to obtain $1-\alpha+\frac{1}{|\mathcal I_2|+1}$. The empirical quantile at a level above $1$ is $+\infty$.
-- source:
--   Romano, Patterson and Candès, Conformalized Quantile Regression, arXiv:1905.03222v1 (2019), Appendix A, Lemma 2 (Inflation of quantiles) and its proof, p. 18; upper bound α + 1/(n+1) as established by the proof (printed: α + 1/n)

import Mathlib
import Definitions.Def_ConformalizedQuantileRegression_Basic

open MeasureTheory ProbabilityTheory

namespace ConformalizedQuantileRegression

theorem quantile_inflation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n) (Z : Fin (n + 1) → Ω → ℝ)
    (hZ : IsExchangeable P Z) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ENNReal.ofReal α ≤
        P {ω | (Z (Fin.last n) ω : EReal) ≤
          empQuantile (Finset.univ.map Fin.castSuccEmb) (fun i => Z i ω) ((1 + 1 / (n : ℝ)) * α)} ∧
    ((∀ᵐ ω ∂P, Function.Injective (fun i => Z i ω)) →
      P {ω | (Z (Fin.last n) ω : EReal) ≤
          empQuantile (Finset.univ.map Fin.castSuccEmb) (fun i => Z i ω) ((1 + 1 / (n : ℝ)) * α)} ≤
        ENNReal.ofReal (α + 1 / ((n : ℝ) + 1))) := by sorry

end ConformalizedQuantileRegression
