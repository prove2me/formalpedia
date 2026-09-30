-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_fiber_trig_pos
-- name    : BirkhoffGlobalSection.TangentialHessian.fiber_trig_pos
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-29T22:42:51.085868+00:00
-- url     : https://prove2.me/theorems/bf215269-7c88-418d-bb5a-ca19409ca30c
-- title:
--   Positivity of the bordered form on a fiber circle from its harmonic coefficients
-- statement:
--   Let $a, b, F, \ell_{00}, \ell_{01}, \ell_{11}, v_0, v_1$ be real numbers. Put
--   $$L_0 = \begin{pmatrix} \ell_{00} & \ell_{01} \\ \ell_{01} & \ell_{11} \end{pmatrix}, \quad M_1 = \begin{pmatrix} -4b & -4a \\ -4a & -12b \end{pmatrix}, \quad M_2 = \begin{pmatrix} 12a & 4b \\ 4b & 4a \end{pmatrix},$$
--   and, for $(x, y)$ on the circle $x^2 + y^2 = F$, let $L = L_0 + x M_1 + y M_2$. Define
--   $$G = F \det L_0 + v^{\mathsf T}\operatorname{adj}(L_0)\,v - 16F^2(a^2+b^2), \qquad \beta_k = F \operatorname{tr}\bigl(\operatorname{adj}(L_0) M_k\bigr) + v^{\mathsf T}\operatorname{adj}(M_k)\,v .$$
--   If $G > 0$ and $F(\beta_1^2 + \beta_2^2) < G^2$, then
--   $$(x^2 + y^2)\det L + v^{\mathsf T}\operatorname{adj}(L)\,v > 0 .$$
--
--   On the circle, the left side is a degree-two trigonometric polynomial in the angle of $(x, y)$:
--   - its first-harmonic coefficients are $\beta_1, \beta_2$;
--   - its second-harmonic coefficients are $-32F(a^2 - b^2)$ and $-64Fab$, of amplitude $32F(a^2+b^2)$;
--   - its constant term minus $F$ times that amplitude is $G$.
--
--   The hypotheses make the constant term dominate both harmonics. With $a = z_1$, $b = z_2$, the matrices $M_1, M_2$ are the Hessians of $b(z) = (-(2Z+\mu)z_2, (2Z-\mu)z_1)$. This is the fiber-elimination step of Grisa, *Exact fiber elimination for the Levi–Civita convexity gates*, Zenodo 21270420 (2026), Lemmas 3.4–3.5 and Theorem 3.7(b).
-- source:
--   Grisa, Exact fiber elimination for the Levi–Civita convexity gates of the planar restricted three-body problem, Zenodo 21270420 (2026), Lemmas 3.4–3.5, Theorem 3.7(b).

import Mathlib.Data.Real.Basic
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace BirkhoffGlobalSection.TangentialHessian

/-- Abstract fiber step: on the circle `x² + y² = F`, the bordered form with `L = L₀ + x M₁ + y M₂`
(`M₁ = [[-4b, -4a], [-4a, -12b]]`, `M₂ = [[12a, 4b], [4b, 4a]]`) is positive once
`G > 0` and `F |β|² < G²`. -/
theorem fiber_trig_pos (x y F l00 l01 l11 v0 v1 a b : ℝ) (hc : x ^ 2 + y ^ 2 = F)
    (hG : 0 < F * (l00 * l11 - l01 ^ 2) + (l11 * v0 ^ 2 - 2 * l01 * v0 * v1 + l00 * v1 ^ 2)
      - 16 * F ^ 2 * (a ^ 2 + b ^ 2))
    (hW : F * ((F * (l11 * (-4 * b) - 2 * l01 * (-4 * a) + l00 * (-12 * b))
          + ((-12 * b) * v0 ^ 2 - 2 * (-4 * a) * v0 * v1 + (-4 * b) * v1 ^ 2)) ^ 2
        + (F * (l11 * (12 * a) - 2 * l01 * (4 * b) + l00 * (4 * a))
          + ((4 * a) * v0 ^ 2 - 2 * (4 * b) * v0 * v1 + (12 * a) * v1 ^ 2)) ^ 2)
      < (F * (l00 * l11 - l01 ^ 2) + (l11 * v0 ^ 2 - 2 * l01 * v0 * v1 + l00 * v1 ^ 2)
          - 16 * F ^ 2 * (a ^ 2 + b ^ 2)) ^ 2) :
    0 < (x ^ 2 + y ^ 2) *
          ((l00 + x * (-4 * b) + y * (12 * a)) * (l11 + x * (-12 * b) + y * (4 * a))
            - (l01 + x * (-4 * a) + y * (4 * b)) ^ 2) +
        ((l11 + x * (-12 * b) + y * (4 * a)) * v0 ^ 2
          - 2 * (l01 + x * (-4 * a) + y * (4 * b)) * v0 * v1
          + (l00 + x * (-4 * b) + y * (12 * a)) * v1 ^ 2) := by sorry

end BirkhoffGlobalSection.TangentialHessian
