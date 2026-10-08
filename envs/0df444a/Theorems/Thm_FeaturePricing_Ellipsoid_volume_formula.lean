-- Prove2me | Theorems.Thm_FeaturePricing_Ellipsoid_volume_formula
-- name    : FeaturePricing.Ellipsoid.volume_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:21:54.420983+00:00
-- url     : https://prove2.me/theorems/0c7f94e1-b745-48bc-bb7e-0ede69a764ba
-- title:
--   §5.1, p. 14 — Vol E(A, a) = V_d · √(∏ᵢ λᵢ(A))
-- statement:
--   Let $A$ be a positive definite $d\times d$ matrix with eigenvalues $\lambda_1(A),\dots,\lambda_d(A)$, and $a\in\mathbb R^d$. Then
--   $$
--   \operatorname{Vol}E(A,a)=V_d\cdot\sqrt{\textstyle\prod_i\lambda_i(A)},
--   $$
--   where $V_d$ is the volume of the Euclidean unit ball in $\mathbb R^d$.
--
--   In the proof of Lemma 1 this formula converts the eigenvalue floor into a lower bound on the volume of the current ellipsoid.
--
--   **Formalization Note** Volume is Lebesgue measure on `Fin d → ℝ` with values in $[0,\infty]$. $V_d$ is written as the volume of `ellipsoidBall 0 1` $=E(I,0)=\{\theta:\theta'\theta\le1\}$, the Euclidean unit ball. The product runs over Mathlib's (unsorted) eigenvalue family of the symmetric matrix $A$; the order is irrelevant for a product.
-- source:
--   Cohen, Lobel, Paes Leme, Feature-Based Dynamic Pricing, Management Science (2020), DOI 10.1287/mnsc.2019.3485 (authors' copy, SSRN 2737045), p. 14, §5.1

import Mathlib
import Definitions.Def_LinearOptimization_Ellipsoid

namespace FeaturePricing.Ellipsoid

open Matrix LinearOptimization MeasureTheory

/-- **§5.1, p. 14.** The volume of the ellipsoid `E(A, a)` is `V_d · √(∏ᵢ λᵢ(A))`, where
`V_d` is the volume of the Euclidean unit ball `E(I, 0) = {θ : θ′θ ≤ 1}` of `ℝ^d`. -/
theorem volume_formula {d : ℕ} (a : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) :
    volume (ellipsoid a A) =
      volume (ellipsoidBall (0 : Fin d → ℝ) 1) *
        ENNReal.ofReal (Real.sqrt (∏ i, hA.isHermitian.eigenvalues i)) := by sorry

end FeaturePricing.Ellipsoid
