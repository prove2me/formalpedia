-- Prove2me | Theorems.Thm_ComplementarySourcing_lemma_2
-- name    : ComplementarySourcing.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:07:28.450416+00:00
-- url     : https://prove2.me/theorems/d6152a2c-6588-4d1b-8b82-cba41a27a6db
-- title:
--   Lemma 2, p.13 — the supplier's best response is the closed form (4)
-- statement:
--   Let $x_m\ge0$, $w\ge0$ and let $\epsilon$ be a realized market risk. A number $y$ is an optimal effort of the supplier, meaning that it maximizes $w\,d(x_m,x_s,\epsilon)-\tfrac12x_s^2$ over $x_s\ge0$, if and only if
--
--   $$y=\begin{cases}0&\text{if }x_m\ge\epsilon,\\ \min\Big(x^0_s(x_m,w),\ \dfrac{\epsilon-x_m}{1+\alpha x_m}\Big)&\text{if }x_m\le\epsilon,\end{cases}\qquad x^0_s(x_m,w)=\mu w(1+\alpha x_m).$$
--
--   The supplier thus never pushes the user experience past $\epsilon$. This response is the second stage of Model (M), and its mirror is the second stage of Model (S).
--
--   Differences from the source:
--   - generalization: ϵ = ϵ_i, i = 1, 2 → every real ε; reason: the two realizations are real numbers, so the printed case is a specialization
--   - generalization: (x_m, w) with 0 ≤ w ≤ r → w ≥ 0, no upper bound and no r; reason: the supplier's problem does not use r, so the printed case is a specialization
--   - reading: "the supplier's optimal investment effort is given by" → iff: y is a best response exactly when y is the formula; reason: "the" optimal effort: the formula is a maximizer and the only one
--   - reading: µ is "a scaling parameter for market size" (p.7), and the page divides by µ (p.13) → 0 < μ; reason: a market-size scale is positive; the page's formulas are undefined at µ = 0
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), Lemma 2, eq. (4), p.13; proof p.A11 and Lemma A3, p.A15

import Mathlib
import Definitions.Def_ComplementarySourcing_IsBestResponse
import Definitions.Def_ComplementarySourcing_supplierStageProfit

namespace ComplementarySourcing

/-- **Lemma 2** (Conditional Supplier Effort): for given `(x_m, w)` and realized `ϵ`, the supplier's
optimal effort is `0` if `x_m ≥ ϵ` and `min(x⁰_s(x_m, w), (ϵ − x_m)/(1 + αx_m))` if `x_m ≤ ϵ`, where
`x⁰_s(x_m, w) = µw(1 + αx_m)`. Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), Lemma 2, eq. (4), p.13 (PDF 13).

**Formalization Note.** The `↔` carries both optimality and uniqueness of the maximizer. It is
stated for every real `ϵ` and every `w ≥ 0`: the supplier's problem does not use `r`. -/
theorem lemma_2 {μ α xm w ε y : ℝ} (hμ : 0 < μ) (hα : 0 ≤ α) (hxm : 0 ≤ xm) (hw : 0 ≤ w) :
    IsBestResponse (Set.Ici 0) (supplierStageProfit μ α xm w ε) y ↔
      (xm ≥ ε → y = 0) ∧
        (xm ≤ ε → y = min (μ * w * (1 + α * xm)) ((ε - xm) / (1 + α * xm))) := by sorry

end ComplementarySourcing
