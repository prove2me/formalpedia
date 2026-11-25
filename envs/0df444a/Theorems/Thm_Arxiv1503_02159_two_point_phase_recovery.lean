-- Prove2me | Theorems.Thm_Arxiv1503_02159_two_point_phase_recovery
-- name    : Arxiv1503_02159.two_point_phase_recovery
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T13:00:19.543353+00:00
-- url     : https://prove2.me/theorems/7cbc0e2e-361c-43c9-9efc-d34dc884baab
-- title:
--   Theorem 2.1: $s_{21}(k)$ from $|s_{21}(k)|^2$ and $|\psi^+|^2$ at two points
-- statement:
--   Let $v$ be real-valued with $v\in L^1_1(\mathbb R)$ and $v(x)=0$ for $x<0$. Let $k>0$, let $\psi^+(\cdot,k)$ be the scattering solution of (1.4) with reflection coefficient to the left $s_{21}=s_{21}(k)$, and write $s_{21}=|s_{21}|e^{i\alpha}$ with $\alpha\in\mathbb R$. Put $a(x)=|\psi^+(x,k)|^2-1$. Let $x_1,x_2<0$ with $x_1-x_2\notin\frac{\pi}{2k}\mathbb Z$. Then
--
--   $$|s_{21}|\begin{pmatrix}\cos\alpha\\ \sin\alpha\end{pmatrix}=\frac{1}{2\sin(2k(x_2-x_1))}\begin{pmatrix}\sin(2kx_2)&-\sin(2kx_1)\\-\cos(2kx_2)&\cos(2kx_1)\end{pmatrix}\begin{pmatrix}a(x_1)-|s_{21}|^2\\ a(x_2)-|s_{21}|^2\end{pmatrix}.$$
--
--   So $s_{21}(k)$ is given explicitly by the phaseless data $S_1(x_1,x_2,k)=\{|s_{21}(k)|^2,|\psi^+(x_1,k)|^2,|\psi^+(x_2,k)|^2\}$.
--
--   **Formalization Note** The matrix identity is stated as its two scalar components. The condition $x_1\ne x_2 \bmod \pi(2k)^{-1}$ is written as $x_1-x_2\ne n\pi/(2k)$ for all integers $n$. The phase $\alpha$ is any real number with $s_{21}=|s_{21}|e^{i\alpha}$ (arbitrary when $s_{21}=0$).
-- source:
--   R. G. Novikov, Phaseless inverse scattering in the one-dimensional case, arXiv:1503.02159v1 (2015), claim c002; Section 2, Theorem 2.1, eqs. (2.1)-(2.3), PDF p. 3 (proof: Section 3, eqs. (3.1)-(3.4), PDF pp. 4-5)

import Mathlib
import Definitions.Def_Arxiv1503_02159_Basic

open MeasureTheory Filter Topology

namespace Arxiv1503_02159

theorem two_point_phase_recovery (v : ℝ → ℝ) (hv : IsAdmissiblePotential v)
    (k : ℝ) (hk : 0 < k) (ψ : ℝ → ℂ) (s21 s22 : ℂ) (hψ : IsScatteringSolution v k ψ s21 s22)
    (α : ℝ) (hα : s21 = (‖s21‖ : ℂ) * Complex.exp (α * Complex.I))
    (x1 x2 : ℝ) (hx1 : x1 < 0) (hx2 : x2 < 0)
    (hx12 : ∀ n : ℤ, x1 - x2 ≠ n * (Real.pi / (2 * k))) :
    ‖s21‖ * Real.cos α = (2 * Real.sin (2 * k * (x2 - x1)))⁻¹ *
        (Real.sin (2 * k * x2) * (phaselessA ψ x1 - ‖s21‖ ^ 2)
          - Real.sin (2 * k * x1) * (phaselessA ψ x2 - ‖s21‖ ^ 2)) ∧
    ‖s21‖ * Real.sin α = (2 * Real.sin (2 * k * (x2 - x1)))⁻¹ *
        (-Real.cos (2 * k * x2) * (phaselessA ψ x1 - ‖s21‖ ^ 2)
          + Real.cos (2 * k * x1) * (phaselessA ψ x2 - ‖s21‖ ^ 2)) := by sorry

end Arxiv1503_02159
