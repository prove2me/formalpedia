-- Prove2me | Theorems.Thm_Arxiv1408_1879_surface_integral_equation
-- name    : Arxiv1408_1879.surface_integral_equation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T11:32:30.651777+00:00
-- url     : https://prove2.me/theorems/fab58174-95ee-4990-9a77-a84ccf98a3cd
-- title:
--   Eqs. (8), (10): the two-way surface integral equation (as proved)
-- statement:
--   Let $k>0$, let $h$ be a continuous surface, let $x\ge0$, and let $f$ be a surface source with
--   $$\int_0^\infty\frac{|f(x')|}{\sqrt{|x-x'|}}\,dx'<\infty.$$
--   Let $\psi_i,\psi_s$ be the incident and scattered reduced fields. Suppose that in the medium below the surface ($z<h(x)$) the scattered field is given by eq. (7), $\psi_s(x,z)=\int_0^\infty G\big((x,z),(x',h(x'))\big)f(x')\,dx'$. Suppose $\psi_s(x,\cdot)$ is continuous as $z\to h(x)$ from the medium, and the total field vanishes on the pressure-release surface, $\psi_i(x,h(x))+\psi_s(x,h(x))=0$. Then
--   $$\psi_i(x,h(x))=-\int_0^\infty G(r_s,r')f(x')\,dx'=-(L+R)f\,(x,h(x)),$$
--   where $r_s=(x,h(x))$ and $r'=(x',h(x'))$ both lie on the surface. This is eq. (8), together with its operator form (10).
--
--   **Formalization Note** Eq. (10) is printed as $\psi_i=(L+R)\,\partial\psi/\partial z$, the opposite sign to eq. (8). The statement follows eq. (8) (as proved). The weighted integrability of $f$ makes the limit $z\to h(x)$ in eq. (7) well defined. The paper takes the existence of this limit for granted. The medium is $z<h(x)$ because $z$ is directed out of the medium (Section 2).
-- source:
--   M. Spivack and O. Rath Spivack, Rough surface backscatter and statistics via extended parabolic integral equation, arXiv:1408.1879v2 (2015), claim c002; Section 3.1, eqs. (7), (8), (10), PDF p. 5

import Mathlib
import Definitions.Def_Arxiv1408_1879_Basic

open MeasureTheory Filter Topology

namespace Arxiv1408_1879

theorem surface_integral_equation (k : ℝ) (hk : 0 < k) (h : ℝ → ℝ) (hh : Continuous h)
    (f : ℝ → ℂ) (x : ℝ) (hx : 0 ≤ x)
    (hf : IntegrableOn (fun x' => f x' / ((Real.sqrt |x - x'| : ℝ) : ℂ)) (Set.Ici 0))
    (ψi ψs : ℝ → ℝ → ℂ)
    (hmedium : ∀ z, z < h x → ψs x z = twoWayField k h f x z)
    (hcont : ContinuousWithinAt (ψs x) (Set.Iio (h x)) (h x))
    (hbc : ψi x (h x) + ψs x (h x) = 0) :
    ψi x (h x) = -twoWayField k h f x (h x) ∧
      ψi x (h x) = -(leftOp k h f x (h x) + rightOp k h f x (h x)) := by sorry

end Arxiv1408_1879
