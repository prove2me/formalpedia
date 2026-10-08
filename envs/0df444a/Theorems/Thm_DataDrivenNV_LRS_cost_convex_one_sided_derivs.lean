-- Prove2me | Theorems.Thm_DataDrivenNV_LRS_cost_convex_one_sided_derivs
-- name    : DataDrivenNV.LRS.cost_convex_one_sided_derivs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:25:16.426564+00:00
-- url     : https://prove2.me/theorems/7ca33ae6-45fc-470e-a475-ca646d90c5b3
-- title:
--   §2, p. 7 — C is convex with ∂₊C(q) = −b + (b+h)F(q) and ∂₋C(q) = −b + (b+h)Pr(D < q)
-- statement:
--   Let $D$ be a real-valued demand with law $\mu$ and $\mathbb E|D|<\infty$, let $b,h>0$, and let $C(q)=\mathbb E[b(D-q)^+ + h(q-D)^+]$ be the expected newsvendor cost. Write $F(q)=\Pr(D\le q)$.
--
--   Then $C$ is convex on $\mathbb R$, and at every $q\in\mathbb R$ it has the right-sided derivative and the left-sided derivative
--   $$\partial_+C(q) = -b + (b+h)F(q), \qquad \partial_-C(q) = -b + (b+h)\Pr(D<q).$$
--
--   The two one-sided derivatives differ exactly at the atoms of $D$. They are what the LRS interval $S^{LRS}_\epsilon$ of display (3) is defined with, and this result links the formulas used in Proposition EC.1 to the derivatives in (3).
--
--   **Formalization Note** The one-sided derivatives are stated as derivatives within $[q,\infty)$ and within $(-\infty,q]$ at $q$. The hypothesis $\mathbb E|D|<\infty$ is the standing assumption that makes $C$ an expectation; without it the Lean integral is $0$.
-- source:
--   Levi, Perakis & Uichanco, The Data-Driven Newsvendor Problem: New Bounds and Insights, authors' accepted manuscript (MIT DSpace), p. 7, §2, second paragraph (attributed to Zipkin 2000)

import Mathlib
import Definitions.Def_DataDrivenNV_LRS_Setting

open MeasureTheory ProbabilityTheory

namespace DataDrivenNV.LRS

/-- §2, p. 7: if `E|D| < ∞`, the expected newsvendor cost `C` is convex on `ℝ`, its right-sided
derivative at `q` is `∂₊C(q) = -b + (b + h) F(q)` and its left-sided derivative at `q` is
`∂₋C(q) = -b + (b + h) Pr(D < q)`. -/
theorem cost_convex_one_sided_derivs (b h : ℝ) (hb : 0 < b) (hh : 0 < h)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ) :
    ConvexOn ℝ Set.univ (expCost μ b h) ∧
      ∀ q : ℝ, HasDerivWithinAt (expCost μ b h) (dPlus μ b h q) (Set.Ici q) q ∧
        HasDerivWithinAt (expCost μ b h) (dMinus μ b h q) (Set.Iic q) q := by sorry

end DataDrivenNV.LRS
