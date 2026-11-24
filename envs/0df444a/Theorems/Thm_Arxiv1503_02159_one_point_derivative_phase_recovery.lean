-- Prove2me | Theorems.Thm_Arxiv1503_02159_one_point_derivative_phase_recovery
-- name    : Arxiv1503_02159.one_point_derivative_phase_recovery
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T13:26:12.309066+00:00
-- url     : https://prove2.me/theorems/99dabc04-3287-4302-aba7-22c0ff468b3f
-- title:
--   Theorem 2.3 (as proved): $s_{21}(k)$ from $|\psi^+|^2$ and its $x$-derivative at one point
-- statement:
--   Let $v$ be real-valued with $v\in L^1_1(\mathbb R)$ and $v(x)=0$ for $x<0$. Let $k>0$, let $\psi^+(\cdot,k)$ be the scattering solution of (1.4) with reflection coefficient to the left $s_{21}(k)$, and let $x<0$. Then $|\psi^+(x,k)|^2-\big(\operatorname{Im}(s_{21}(k)e^{-2ikx})\big)^2>0$ and
--
--   $$\operatorname{Re}\big(s_{21}(k)e^{-2ikx}\big)=-1+\Big(|\psi^+(x,k)|^2-\big|\operatorname{Im}\big(s_{21}(k)e^{-2ikx}\big)\big|^2\Big)^{1/2},$$
--
--   $$\operatorname{Im}\big(s_{21}(k)e^{-2ikx}\big)=\frac{1}{4k}\,\frac{d|\psi^+(x,k)|^2}{dx},$$
--
--   with the positive square root. So $s_{21}(k)$ is given explicitly by $S_3(x,k)=\{|\psi^+(x,k)|^2,\ d|\psi^+(x,k)|^2/dx\}$.
--
--   **Formalization Note** The paper prints (2.5)-(2.6) with the factor $e^{-ikx}$; its proof, eqs. (3.9)-(3.10), establishes them with $e^{-2ikx}$, and the printed version is false in general (for $s_{21}=0.6e^{0.9i}$, $k=1.3$, $x=-0.7$ both printed identities fail). The statement is the version the proof establishes. The requirement that the root be positive is stated as the first conclusion; the root itself is Lean's nonnegative square root.
-- source:
--   R. G. Novikov, Phaseless inverse scattering in the one-dimensional case, arXiv:1503.02159v1 (2015), claim c004; Section 2, Theorem 2.3, eqs. (2.5)-(2.6), PDF p. 4 (proof: Section 3, eqs. (3.9)-(3.10), PDF p. 6); stated with e^{-2ikx} as in the proof

import Mathlib
import Definitions.Def_Arxiv1503_02159_Basic

open MeasureTheory Filter Topology

namespace Arxiv1503_02159

theorem one_point_derivative_phase_recovery (v : ℝ → ℝ) (hv : IsAdmissiblePotential v)
    (k : ℝ) (hk : 0 < k) (ψ : ℝ → ℂ) (s21 s22 : ℂ) (hψ : IsScatteringSolution v k ψ s21 s22)
    (x : ℝ) (hx : x < 0) :
    0 < ‖ψ x‖ ^ 2 - (s21 * Complex.exp (-(2 * k * x * Complex.I))).im ^ 2 ∧
    (s21 * Complex.exp (-(2 * k * x * Complex.I))).re =
      -1 + Real.sqrt (‖ψ x‖ ^ 2 - (s21 * Complex.exp (-(2 * k * x * Complex.I))).im ^ 2) ∧
    (s21 * Complex.exp (-(2 * k * x * Complex.I))).im =
      1 / (4 * k) * deriv (fun y => ‖ψ y‖ ^ 2) x := by sorry

end Arxiv1503_02159
