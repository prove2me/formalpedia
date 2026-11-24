-- Prove2me | Theorems.Thm_ConformalizedQuantileRegression_inflated_quantile_iff
-- name    : ConformalizedQuantileRegression.inflated_quantile_iff
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:41:03.386798+00:00
-- url     : https://prove2.me/theorems/ae77f13f-c984-41a0-9daa-525e5ecf85a3
-- title:
--   Lemma 2 (proof): $Z_{n+1}\le\hat Q_n((1+\frac1n)\alpha)$ iff $Z_{n+1}\le\hat Q_{n+1}(\alpha)$
-- statement:
--   Let $n\ge1$, let $z_1,\dots,z_{n+1}$ be real numbers and let $\alpha\in(0,1)$. Write $\hat Q_n$ for the empirical quantile function of $z_1,\dots,z_n$ and $\hat Q_{n+1}$ for that of $z_1,\dots,z_{n+1}$. Then
--
--   $$z_{n+1}\le\hat Q_n\big((1+\tfrac1n)\alpha\big)\quad\Longleftrightarrow\quad z_{n+1}\le\hat Q_{n+1}(\alpha).$$
--
--   This deterministic identity reduces the inflated quantile of $n$ values to the plain quantile of $n+1$ values, which is how Lemma 2 follows from Lemma 1.
--
--   **Formalization Note** When $(1+\frac1n)\alpha>1$ the left-hand quantile is $+\infty$ (the infimum of the empty set in the extended reals), and the left-hand side holds trivially; the paper's proof covers this case only through its formula $Z_{(\lceil\alpha(n+1)\rceil,n)}$ with $\lceil\alpha(n+1)\rceil=n+1$.
-- source:
--   Romano, Patterson and Candès, Conformalized Quantile Regression, arXiv:1905.03222v1 (2019), Appendix A, proof of Lemma 2 (Inflation of quantiles), unnumbered display, p. 18

import Mathlib
import Definitions.Def_ConformalizedQuantileRegression_Basic

open MeasureTheory ProbabilityTheory

namespace ConformalizedQuantileRegression

theorem inflated_quantile_iff {n : ℕ} (hn : 0 < n) (z : Fin (n + 1) → ℝ) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) :
    (z (Fin.last n) : EReal) ≤ empQuantile (Finset.univ.map Fin.castSuccEmb) z ((1 + 1 / (n : ℝ)) * α) ↔
      (z (Fin.last n) : EReal) ≤ empQuantile Finset.univ z α := by sorry

end ConformalizedQuantileRegression
