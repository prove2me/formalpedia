-- Prove2me | Theorems.Thm_DualSSD_MeanRisk_hDiam_eq_min
-- name    : DualSSD.MeanRisk.hDiam_eq_min
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:05:20.30532+00:00
-- url     : https://prove2.me/theorems/a9bc3d1a-adaa-40b4-a29d-0f1b83940357
-- title:
--   Lemma 3.4 — $h_X(p)$ is the minimal weighted mean absolute deviation, attained at every $p$-quantile
-- statement:
--   Let $X$ be an integrable random variable and $p\in(0,1)$. Then
--
--   $$h_X(p)=\min_{\xi\in\mathbb R}E\{\max(p(X-\xi),(1-p)(\xi-X))\},$$
--
--   that is, $h_X(p)$ is a lower bound of the function $\xi\mapsto E\{\max(p(X-\xi),(1-p)(\xi-X))\}$ and is one of its values; moreover the minimum is attained at every $p$-quantile of $X$.
--
--   The lemma identifies the vertical diameter of the dual dispersion space with a weighted mean absolute deviation from a quantile, and gives the stochastic-programming form of the risk measure.
-- source:
--   Ogryczak, Ruszczyński, Dual Stochastic Dominance and Related Mean-Risk Models, SIAM J. Optim. 13 (2002), p. 66, Lemma 3.4, eq. (3.7)

import Mathlib
import Definitions.Def_DualSSD_MeanRisk_gini

namespace DualSSD.MeanRisk

open MeasureTheory

/-- **Lemma 3.4** (Ogryczak–Ruszczyński 2002, p. 66). For an integrable `X` and every
`p ∈ (0, 1)`, `h_X(p) = min_{ξ ∈ ℝ} E{max(p(X − ξ), (1 − p)(ξ − X))}`: the value `h_X(p)` is the
least value of `ξ ↦ E{max(p(X − ξ), (1 − p)(ξ − X))}` (a lower bound that is attained), and the
minimum is attained at every `p`-quantile of `X`. -/
theorem hDiam_eq_min {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    IsLeast (Set.range fun ξ : ℝ => ∫ ω, max (p * (X ω - ξ)) ((1 - p) * (ξ - X ω)) ∂P)
        (hDiam P X p) ∧
      ∀ ξ : ℝ, IsPQuantile P X p ξ →
        ∫ ω, max (p * (X ω - ξ)) ((1 - p) * (ξ - X ω)) ∂P = hDiam P X p := by sorry

end DualSSD.MeanRisk
