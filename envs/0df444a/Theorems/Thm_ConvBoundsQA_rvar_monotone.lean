-- Prove2me | Theorems.Thm_ConvBoundsQA_rvar_monotone
-- name    : ConvBoundsQA.rvar_monotone
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:27:59.268163+00:00
-- url     : https://prove2.me/theorems/89da7e24-1db1-4a5b-9531-78aa1e2ae74b
-- title:
--   p.8 before (10) — $R_{t,s}\le R_{t+s-\beta_0,\beta_0}$
-- statement:
--   Let $\mu$ be a Borel probability measure on $\mathbb R$ and $0\le t<t+s\le1$. For every $\beta_0\in[s,t+s]$,
--   $$
--   R_{t,s}(\mu)\le R_{t+s-\beta_0,\beta_0}(\mu).
--   $$
--   Both sides average the quantile of $\mu$ over a window with the same left end $1-t-s$; the right-hand window $[1-t-s,\,1-t-s+\beta_0]$ extends the left-hand one $[1-t-s,\,1-t]$ to the right.
--
--   This is the first inequality of (10), which, combined with the RVaR aggregation inequality, gives the convolution bound (11).
--
--   **Formalization Note** RVaR values are extended reals. Lean's $R$ is total, with value $-\infty$ where the mean $R_{0,1}$ is undefined.
--
--   Differences from the source:
--   - encoding: quantiles and RVaR values in $[-\infty,\infty]$ → `EReal`, with $R_{\beta,\alpha}$ the difference of the integrals of the positive and negative parts of the quantile; reason: Lean convention; same values wherever the source defines them
--   - generalization: $R_{0,1}$ (the mean) is defined only on $\mathcal M_1$, so the page's inequality speaks of defined values → the inequality for every probability measure, with $R_{0,1}(\mu)=-\infty$ when the mean is undefined; reason: the undefined value occurs only at $(t,s)=(0,1)$, where both sides coincide, or at $\beta_0=t+s=1$ with $t>0$, where the left side is an LES of a measure with an infinite lower tail, hence $-\infty$; on defined values it is the source's statement
-- source:
--   Blanchet, Lam, Liu, Wang, Convolution Bounds on Quantile Aggregation, arXiv:2007.09320v5, §4, p.8, before (10)

import Mathlib
import Definitions.Def_ConvBoundsQA_R

open MeasureTheory

namespace ConvBoundsQA

/-- The monotonicity used in (10): for `0 ⩽ t < t + s ⩽ 1` and `β₀ ∈ [s, t + s]`,
`R_{t,s}(μ) ⩽ R_{t+s−β₀,β₀}(μ)` for every probability measure `μ` on `ℝ`
(Blanchet, Lam, Liu, Wang, *Convolution Bounds on Quantile Aggregation*, arXiv:2007.09320v5, §4, p.8:
"noting that `R_{t,s} ⩽ R_{t+s−β₀,β₀}`").

**Formalization Note** The page compares the averages of the quantile over `[1 − t − s, 1 − t]` and
over `[1 − t − s, 1 − t − s + β₀]`. Values lie in `EReal`. `R` is total in Lean: when `R_{0,1}(μ)` (the
mean) is undefined its value is `−∞`, and the inequality is stated for that value as well. -/
theorem rvar_monotone (μ : Measure ℝ) [IsProbabilityMeasure μ] (t s β₀ : ℝ) (ht : 0 ≤ t)
    (hts : t < t + s) (hts1 : t + s ≤ 1) (hβ₀ : β₀ ∈ Set.Icc s (t + s)) :
    R t s μ ≤ R (t + s - β₀) β₀ μ := by sorry

end ConvBoundsQA
