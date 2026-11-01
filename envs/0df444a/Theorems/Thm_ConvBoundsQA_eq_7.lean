-- Prove2me | Theorems.Thm_ConvBoundsQA_eq_7
-- name    : ConvBoundsQA.eq_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:27:44.890064+00:00
-- url     : https://prove2.me/theorems/c540af44-e35c-434b-aae1-9ffac467f5c3
-- title:
--   Display (7) — quantiles as limits of RVaR
-- statement:
--   Let $\mu$ be a Borel probability measure on $\mathbb R$ and $\beta\in(0,1)$. Then the left and right quantiles at level $1-\beta$ are the limits of RVaR over shrinking windows on either side:
--   $$
--   \lim_{\alpha\downarrow0}R_{\beta,\alpha}(\mu)=q^-_{1-\beta}(\mu)\qquad\text{and}\qquad\lim_{\alpha\downarrow0}R_{\beta-\alpha,\alpha}(\mu)=q^+_{1-\beta}(\mu).
--   $$
--
--   This is how quantile results (Theorem 2) are obtained from RVaR results (Theorem 1) by letting the window width $s\downarrow0$.
--
--   **Formalization Note** The limits are taken in `EReal` as $\alpha\to0^+$; both limits are finite for $\beta\in(0,1)$.
--
--   Differences from the source:
--   - encoding: quantiles and RVaR values in $[-\infty,\infty]$ → `EReal`, with $R_{\beta,\alpha}$ the difference of the integrals of the positive and negative parts of the quantile; reason: Lean convention; same values wherever the source defines them
-- source:
--   Blanchet, Lam, Liu, Wang, Convolution Bounds on Quantile Aggregation, arXiv:2007.09320v5, (7), p.7

import Mathlib
import Definitions.Def_ConvBoundsQA_qPlus
import Definitions.Def_ConvBoundsQA_R

open MeasureTheory Filter Topology

namespace ConvBoundsQA

/-- Display (7): for `β ∈ (0, 1)` and every probability measure `μ` on `ℝ`,
`lim_{α↓0} R_{β,α}(μ) = q⁻_{1−β}(μ)` and `lim_{α↓0} R_{β−α,α}(μ) = q⁺_{1−β}(μ)`
(Blanchet, Lam, Liu, Wang, *Convolution Bounds on Quantile Aggregation*, arXiv:2007.09320v5, (7), p.7).

**Formalization Note** The limits are taken in `EReal` along `α → 0⁺` (`𝓝[>] 0`); for `β ∈ (0, 1)`
both limits are real numbers. -/
theorem eq_7 (μ : Measure ℝ) [IsProbabilityMeasure μ] (β : ℝ) (hβ : β ∈ Set.Ioo 0 1) :
    Tendsto (fun α => R β α μ) (𝓝[>] 0) (𝓝 (qMinus (1 - β) μ)) ∧
      Tendsto (fun α => R (β - α) α μ) (𝓝[>] 0) (𝓝 (qPlus (1 - β) μ)) := by sorry

end ConvBoundsQA
