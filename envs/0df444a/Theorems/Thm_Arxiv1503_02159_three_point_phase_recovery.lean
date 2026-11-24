-- Prove2me | Theorems.Thm_Arxiv1503_02159_three_point_phase_recovery
-- name    : Arxiv1503_02159.three_point_phase_recovery
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T13:13:52.428015+00:00
-- url     : https://prove2.me/theorems/0cc688a3-531c-4213-9fed-a47f8b4db025
-- title:
--   Theorem 2.2: $s_{21}(k)$ from $|\psi^+|^2$ at three points
-- statement:
--   Let $v$ be real-valued with $v\in L^1_1(\mathbb R)$ and $v(x)=0$ for $x<0$. Let $k>0$, let $\psi^+(\cdot,k)$ be the scattering solution of (1.4) with reflection coefficient to the left $s_{21}=s_{21}(k)=|s_{21}|e^{i\alpha}$, $\alpha\in\mathbb R$, and put $a(x)=|\psi^+(x,k)|^2-1$. Let $x_1,x_2,x_3<0$ with $x_i-x_j\notin\frac{\pi}{k}\mathbb Z$ for $i\ne j$. Then
--
--   $$|s_{21}|\begin{pmatrix}\cos\alpha\\ \sin\alpha\end{pmatrix}=\frac{1}{8\sin(k(x_2-x_3))\sin(k(x_2-x_1))\sin(k(x_1-x_3))}\begin{pmatrix}\sin(2kx_3)-\sin(2kx_1)&-\sin(2kx_2)+\sin(2kx_1)\\-\cos(2kx_3)+\cos(2kx_1)&\cos(2kx_2)-\cos(2kx_1)\end{pmatrix}\begin{pmatrix}a(x_2)-a(x_1)\\ a(x_3)-a(x_1)\end{pmatrix}.$$
--
--   So $s_{21}(k)$ is given explicitly by $|\psi^+(\cdot,k)|^2$ at three points, without $|s_{21}(k)|^2$.
--
--   **Formalization Note** The matrix identity is stated as its two scalar components. The paper prints the hypothesis as "$x_1\ne x_2 \bmod(\pi k^{-1})$ if $i\ne j$"; it is read as $x_i\ne x_j \bmod \pi k^{-1}$ for all $i\ne j$, the reading of (A2) in the introduction and the condition under which the determinant (3.8) is nonzero.
-- source:
--   R. G. Novikov, Phaseless inverse scattering in the one-dimensional case, arXiv:1503.02159v1 (2015), claim c006; Section 2, Theorem 2.2, eqs. (2.1), (2.2), (2.4), PDF p. 4 (proof: Section 3, eqs. (3.5)-(3.8), PDF pp. 5-6)

import Mathlib
import Definitions.Def_Arxiv1503_02159_Basic

open MeasureTheory Filter Topology

namespace Arxiv1503_02159

theorem three_point_phase_recovery (v : ℝ → ℝ) (hv : IsAdmissiblePotential v)
    (k : ℝ) (hk : 0 < k) (ψ : ℝ → ℂ) (s21 s22 : ℂ) (hψ : IsScatteringSolution v k ψ s21 s22)
    (α : ℝ) (hα : s21 = (‖s21‖ : ℂ) * Complex.exp (α * Complex.I))
    (x1 x2 x3 : ℝ) (hx1 : x1 < 0) (hx2 : x2 < 0) (hx3 : x3 < 0)
    (hx12 : ∀ n : ℤ, x1 - x2 ≠ n * (Real.pi / k))
    (hx13 : ∀ n : ℤ, x1 - x3 ≠ n * (Real.pi / k))
    (hx23 : ∀ n : ℤ, x2 - x3 ≠ n * (Real.pi / k)) :
    ‖s21‖ * Real.cos α = (8 * (Real.sin (k * (x2 - x3)) * Real.sin (k * (x2 - x1)) *
          Real.sin (k * (x1 - x3))))⁻¹ *
        ((Real.sin (2 * k * x3) - Real.sin (2 * k * x1)) * (phaselessA ψ x2 - phaselessA ψ x1)
          + (-Real.sin (2 * k * x2) + Real.sin (2 * k * x1)) *
            (phaselessA ψ x3 - phaselessA ψ x1)) ∧
    ‖s21‖ * Real.sin α = (8 * (Real.sin (k * (x2 - x3)) * Real.sin (k * (x2 - x1)) *
          Real.sin (k * (x1 - x3))))⁻¹ *
        ((-Real.cos (2 * k * x3) + Real.cos (2 * k * x1)) * (phaselessA ψ x2 - phaselessA ψ x1)
          + (Real.cos (2 * k * x2) - Real.cos (2 * k * x1)) *
            (phaselessA ψ x3 - phaselessA ψ x1)) := by sorry

end Arxiv1503_02159
