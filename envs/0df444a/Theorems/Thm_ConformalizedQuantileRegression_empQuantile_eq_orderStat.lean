-- Prove2me | Theorems.Thm_ConformalizedQuantileRegression_empQuantile_eq_orderStat
-- name    : ConformalizedQuantileRegression.empQuantile_eq_orderStat
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:40:00.152396+00:00
-- url     : https://prove2.me/theorems/6d31c99a-113c-4b46-a555-6c1ad05a97e0
-- title:
--   Appendix A: explicit formula $\hat Q_n(\alpha)=Z_{(\lceil\alpha n\rceil)}$
-- statement:
--   Let $n\ge1$, let $z_1,\dots,z_n$ be real numbers and let $\alpha\in(0,1)$. The empirical quantile $\hat Q_n(\alpha)=\inf\{z\in\mathbb{R}:\alpha\le\hat F_n(z)\}$, with $\hat F_n(z)=\frac1n\sum_{i=1}^n1\{z_i\le z\}$, is the $\lceil\alpha n\rceil$-th smallest value:
--
--   $$\hat Q_n(\alpha)=z_{(\lceil\alpha n\rceil)}.$$
--
--   This turns the inf-definition of the empirical quantile into an order statistic, the form in which the quantiles of Algorithm 1 are computed.
-- source:
--   Romano, Patterson and Candès, Conformalized Quantile Regression, arXiv:1905.03222v1 (2019), Appendix A, explicit formula for the empirical quantile function (unnumbered display), p. 18

import Mathlib
import Definitions.Def_ConformalizedQuantileRegression_Basic

open MeasureTheory ProbabilityTheory

namespace ConformalizedQuantileRegression

theorem empQuantile_eq_orderStat {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) :
    empQuantile Finset.univ z α = (orderStat Finset.univ z ⌈α * n⌉₊ : EReal) := by sorry

end ConformalizedQuantileRegression
