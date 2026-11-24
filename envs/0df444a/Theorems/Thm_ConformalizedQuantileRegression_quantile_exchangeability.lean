-- Prove2me | Theorems.Thm_ConformalizedQuantileRegression_quantile_exchangeability
-- name    : ConformalizedQuantileRegression.quantile_exchangeability
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:40:25.652279+00:00
-- url     : https://prove2.me/theorems/2ad22fe7-ad0c-4944-bfe3-6b2930169b59
-- title:
--   Lemma 1: quantiles and exchangeability
-- statement:
--   Let $n\ge1$ and let $Z_1,\dots,Z_n$ be exchangeable real random variables, and let $\hat Q_n$ be their empirical quantile function. For every $\alpha\in(0,1)$,
--
--   $$\mathbb{P}\{Z_n\le\hat Q_n(\alpha)\}\ge\alpha.$$
--
--   If moreover $Z_1,\dots,Z_n$ are almost surely distinct, then also
--
--   $$\mathbb{P}\{Z_n\le\hat Q_n(\alpha)\}\le\alpha+\frac1n.$$
--
--   The probabilities are over all of $Z_1,\dots,Z_n$. This is the basic rank argument behind every coverage guarantee of the paper.
--
--   **Formalization Note** $Z_n$ is the variable with index $n-1$ in Lean's $0$-based indexing. "Almost surely distinct" is the statement that almost surely $i\mapsto Z_i$ is injective. The empirical quantile is valued in the extended reals; for $\alpha\in(0,1)$ it is finite.
-- source:
--   Romano, Patterson and Candès, Conformalized Quantile Regression, arXiv:1905.03222v1 (2019), Appendix A, Lemma 1 (Quantiles and exchangeability), p. 18

import Mathlib
import Definitions.Def_ConformalizedQuantileRegression_Basic

open MeasureTheory ProbabilityTheory

namespace ConformalizedQuantileRegression

theorem quantile_exchangeability {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n) (Z : Fin n → Ω → ℝ) (hZ : IsExchangeable P Z)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ENNReal.ofReal α ≤
        P {ω | (Z ⟨n - 1, by omega⟩ ω : EReal) ≤ empQuantile Finset.univ (fun i => Z i ω) α} ∧
    ((∀ᵐ ω ∂P, Function.Injective (fun i => Z i ω)) →
      P {ω | (Z ⟨n - 1, by omega⟩ ω : EReal) ≤ empQuantile Finset.univ (fun i => Z i ω) α} ≤
        ENNReal.ofReal (α + 1 / (n : ℝ))) := by sorry

end ConformalizedQuantileRegression
