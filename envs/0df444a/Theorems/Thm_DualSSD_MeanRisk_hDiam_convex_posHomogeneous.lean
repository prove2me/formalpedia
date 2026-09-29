-- Prove2me | Theorems.Thm_DualSSD_MeanRisk_hDiam_convex_posHomogeneous
-- name    : DualSSD.MeanRisk.hDiam_convex_posHomogeneous
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:06:04.722986+00:00
-- url     : https://prove2.me/theorems/8cdf3904-9c98-4e4c-a989-9ba689419b43
-- title:
--   Lemma 5.1 — $X\mapsto h_X(p)$ is convex and positively homogeneous on $L_1$
-- statement:
--   For every $p\in[0,1]$ the functional $X\mapsto h_X(p)=\mu_Xp-F_X^{(-2)}(p)$ is convex and positively homogeneous on $L_1(\Omega,P)$: for $X,Y\in L_1$ and $\beta\in[0,1]$,
--
--   $$h_{\beta X+(1-\beta)Y}(p)\le\beta h_X(p)+(1-\beta)h_Y(p),\qquad h_{cX}(p)=c\,h_X(p)\ \ (c>0).$$
--
--   Convexity of the risk functional makes the mean–risk problems of the paper convex optimization problems.
--
--   **Formalization Note** The functional is evaluated on the function represented by an $L_1$ element, and homogeneity is stated for the $L_1$ element $c\cdot X$; the value depends only on the law, so the choice of representative does not matter.
-- source:
--   Ogryczak, Ruszczyński, Dual Stochastic Dominance and Related Mean-Risk Models, SIAM J. Optim. 13 (2002), p. 73, Lemma 5.1

import Mathlib
import Definitions.Def_DualSSD_MeanRisk_gini

namespace DualSSD.MeanRisk

open MeasureTheory

/-- **Lemma 5.1** (Ogryczak–Ruszczyński 2002, p. 73). For every `p ∈ [0, 1]` the functional
`X ↦ h_X(p)` of (3.6) is convex and positively homogeneous on `L_1`. The functional is evaluated
on the coercion `⇑X` of an `L_1` element; positive homogeneity is stated for the `L_1` element
`c • X`. -/
theorem hDiam_convex_posHomogeneous {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    ConvexOn ℝ Set.univ (fun X : Lp ℝ 1 P => hDiam P (⇑X) p) ∧
      ∀ c : ℝ, 0 < c → ∀ X : Lp ℝ 1 P, hDiam P ⇑(c • X) p = c * hDiam P (⇑X) p := by sorry

end DualSSD.MeanRisk
