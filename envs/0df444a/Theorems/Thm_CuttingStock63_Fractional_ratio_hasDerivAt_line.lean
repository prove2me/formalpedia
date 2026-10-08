-- Prove2me | Theorems.Thm_CuttingStock63_Fractional_ratio_hasDerivAt_line
-- name    : CuttingStock63.Fractional.ratio_hasDerivAt_line
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:01:43.8319+00:00
-- url     : https://prove2.me/theorems/8c92d95c-be5d-4cc4-9edd-bdc424a53b58
-- title:
--   Customer Tolerances, p. 883, eq. (5), first line — dζ/dx_j = [z₂(dz₁/dx_j) − z₁(dz₂/dx_j)]/z₂²
-- statement:
--   Let $c,d,x,v\in\mathbb R^n$ with $z_2=\sum_i d_ix_i\ne 0$, and write
--   $$z_1=\sum_i c_ix_i,\qquad \frac{dz_1}{dx_j}=\sum_i c_iv_i,\qquad \frac{dz_2}{dx_j}=\sum_i d_iv_i$$
--   for the values of the two linear functions at $x$ and their rates of change in the direction $v$. Then $\tau\mapsto\zeta(x+\tau v)=z_1(x+\tau v)/z_2(x+\tau v)$ is differentiable at $\tau=0$ with derivative
--   $$\frac{d\zeta}{dx_j}=\frac{z_2\,\dfrac{dz_1}{dx_j}-z_1\,\dfrac{dz_2}{dx_j}}{z_2^{2}} .$$
--   When $v$ is the edge direction of a nonbasic variable $x_j$, this is the rate of change of the objective $\zeta=z_1/z_2$ as $x_j$ is increased with the other nonbasic variables kept at zero, which is the quantity the simplex test inspects.
--
--   **Formalization Note** The statement holds for every direction $v$; the edge direction of $x_j$ is the special case used on p. 883. The hypothesis $z_2\ne0$ is the page's standing "domain where the denominator does not vanish"; without it Lean's division by zero would give a meaningless value. Only the first line of (5) is stated here; the second and third lines express the same quantity through the rows $(1,0,\Pi^1)$ and $(0,1,\Pi^2)$ of the basis inverse.
-- source:
--   Gilmore & Gomory, A linear programming approach to the cutting stock problem—Part II, Opns. Res. 11 (1963), p. 883, Customer Tolerances, eq. (5), first line

import Mathlib
import Definitions.Def_DermanSeqDecisions_LinProg_LinearFractional

namespace CuttingStock63.Fractional
open DermanSeqDecisions.LinProg
theorem ratio_hasDerivAt_line {n : ℕ} (c d x v : Fin n → ℝ) (hx : ∑ i, d i * x i ≠ 0) :
    HasDerivAt (fun τ : ℝ => fracObj c d (x + τ • v))
      (((∑ i, d i * x i) * (∑ i, c i * v i) - (∑ i, c i * x i) * (∑ i, d i * v i)) /
        (∑ i, d i * x i) ^ 2) 0 := by sorry
end CuttingStock63.Fractional
