-- Prove2me | Theorems.Thm_Arxiv1503_02159_reflection_coefficient_from_psi
-- name    : Arxiv1503_02159.reflection_coefficient_from_psi
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T12:48:39.456549+00:00
-- url     : https://prove2.me/theorems/e3a1ccea-2cf9-47e0-a968-0b7a37faaa13
-- title:
--   Eq. (1.7): the reflection coefficient from the scattering solution at one point
-- statement:
--   Let $v$ be real-valued with $v\in L^1_1(\mathbb R)$ and $v(x)=0$ for $x<0$. Let $k>0$ and let $\psi^+(\cdot,k)$ be the scattering solution of $-\psi''+v\psi=k^2\psi$ with reflection coefficient to the left $s_{21}(k)$, as in (1.4). Then for every $x<0$,
--
--   $$s_{21}(k)=e^{ikx}\psi^+(x,k)-e^{2ikx}.$$
--
--   Thus the complex value of $\psi^+$ at a single point to the left of the support of $v$ determines $s_{21}(k)$; this reduces Problem 1.1b to Problem 1.1a.
-- source:
--   R. G. Novikov, Phaseless inverse scattering in the one-dimensional case, arXiv:1503.02159v1 (2015), claim c001; Section 1, eq. (1.7), PDF p. 2

import Mathlib
import Definitions.Def_Arxiv1503_02159_Basic

open MeasureTheory Filter Topology

namespace Arxiv1503_02159

theorem reflection_coefficient_from_psi (v : ℝ → ℝ) (hv : IsAdmissiblePotential v)
    (k : ℝ) (hk : 0 < k) (ψ : ℝ → ℂ) (s21 s22 : ℂ) (hψ : IsScatteringSolution v k ψ s21 s22)
    (x : ℝ) (hx : x < 0) :
    s21 = Complex.exp (k * x * Complex.I) * ψ x - Complex.exp (2 * k * x * Complex.I) := by sorry

end Arxiv1503_02159
