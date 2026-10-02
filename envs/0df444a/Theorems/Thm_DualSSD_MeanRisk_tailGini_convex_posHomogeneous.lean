-- Prove2me | Theorems.Thm_DualSSD_MeanRisk_tailGini_convex_posHomogeneous
-- name    : DualSSD.MeanRisk.tailGini_convex_posHomogeneous
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:06:31.097171+00:00
-- url     : https://prove2.me/theorems/018c108d-ddf3-4ba2-8948-6561733a520f
-- title:
--   Lemma 5.2 — $X\mapsto G_X(p)$ is convex and positively homogeneous on $L_1$
-- statement:
--   For every $p\in(0,1]$ the functional
--
--   $$X\mapsto G_X(p)=\frac{2}{p^2}\int_0^p\bigl(\mu_X\alpha-F_X^{(-2)}(\alpha)\bigr)\,d\alpha$$
--
--   is convex and positively homogeneous on $L_1(\Omega,P)$. With $p=1$ it gives convexity of the Gini mean difference $\Gamma_X=G_X(1)$, hence concavity of the mean–Gini objective $\mu_X-\lambda\Gamma_X$.
--
--   **Formalization Note** Same conventions as Lemma 5.1: evaluation on the function of an $L_1$ element, homogeneity for the $L_1$ element $c\cdot X$.
-- source:
--   Ogryczak, Ruszczyński, Dual Stochastic Dominance and Related Mean-Risk Models, SIAM J. Optim. 13 (2002), p. 73, Lemma 5.2

import Mathlib
import Definitions.Def_DualSSD_MeanRisk_gini

namespace DualSSD.MeanRisk

open MeasureTheory

/-- **Lemma 5.2** (Ogryczak–Ruszczyński 2002, p. 73). For every `p ∈ (0, 1]` the functional
`X ↦ G_X(p)` of (4.8) is convex and positively homogeneous on `L_1`. -/
theorem tailGini_convex_posHomogeneous {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p : ℝ) (hp : p ∈ Set.Ioc (0 : ℝ) 1) :
    ConvexOn ℝ Set.univ (fun X : Lp ℝ 1 P => tailGini P (⇑X) p) ∧
      ∀ c : ℝ, 0 < c → ∀ X : Lp ℝ 1 P, tailGini P ⇑(c • X) p = c * tailGini P (⇑X) p := by sorry

end DualSSD.MeanRisk
