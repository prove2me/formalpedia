-- Prove2me | Theorems.Thm_ContrastiveDuality_sphere_inner_beta
-- name    : ContrastiveDuality.sphere_inner_beta
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:34:25.300857+00:00
-- url     : https://prove2.me/theorems/9ea27f44-fdf2-40a5-94eb-236198aee018
-- title:
--   Lemma C.1: the dot product of two independent uniform unit vectors is Beta distributed
-- statement:
--   Let $D\ge2$, and let $X,Y$ be independent random vectors on a probability space, each uniformly distributed on the unit sphere $S^{D-1}\subset\mathbb{R}^D$. Then
--
--   $$\frac{X^TY+1}{2}\sim\operatorname{Beta}\Big(\frac{D-1}{2},\frac{D-1}{2}\Big).$$
--
--   **Formalization Note** The conclusion is stated as equality of the law of $(X^TY+1)/2$ with Mathlib's Beta distribution. The paper states the lemma for every $D$; the hypothesis $D\ge2$ is added because for $D=1$ the shape parameters are $0$, no Beta distribution exists, and $X^TY=\pm1$ with probability $1/2$ each. $X$ and $Y$ are assumed measurable.
-- source:
--   Garrido, Chen, Bardes, Najman and LeCun, On the duality between contrastive and non-contrastive self-supervised learning, arXiv:2206.02574v3 (ICLR 2023), Appendix C, Lemma C.1, eq. (23), pp. 14-15

import Mathlib
import Definitions.Def_ContrastiveDuality_Basic

open MeasureTheory ProbabilityTheory Matrix

namespace ContrastiveDuality

theorem sphere_inner_beta {D : ℕ} (hD : 2 ≤ D) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → EuclideanSpace ℝ (Fin D))
    (hX : Measurable X) (hY : Measurable Y)
    (hXlaw : P.map X = uniformSphere D) (hYlaw : P.map Y = uniformSphere D)
    (hXY : IndepFun X Y P) :
    P.map (fun ω => (inner ℝ (X ω) (Y ω) + 1) / 2) =
      betaMeasure (((D : ℝ) - 1) / 2) (((D : ℝ) - 1) / 2) := by sorry

end ContrastiveDuality
