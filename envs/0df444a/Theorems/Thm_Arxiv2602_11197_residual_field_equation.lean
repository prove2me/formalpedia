-- Prove2me | Theorems.Thm_Arxiv2602_11197_residual_field_equation
-- name    : Arxiv2602_11197.residual_field_equation
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T20:17:18.517655+00:00
-- url     : https://prove2.me/theorems/96815f50-e3e6-4332-9c7e-727f3e8e7825
-- title:
--   Eq. (2) (as derived): the residual field equation
-- statement:
--   Let $\Omega=(0,L_1)\times(0,L_2)$ with $L_1,L_2>0$, and let $\omega>0$. Let $v$ and $v_{\mathrm{bg}}$ be wavespeeds that are positive on $\overline\Omega$, and let $s$ be a source. Suppose $p$ solves the Helmholtz problem (1) with wavespeed $v$ and source $s$, and $p_{\mathrm{bg}}$ solves (1) with wavespeed $v_{\mathrm{bg}}$ and the same source $s$. Put $\delta p=p-p_{\mathrm{bg}}$ and $\delta m=v^{-2}-v_{\mathrm{bg}}^{-2}$. Then the following hold.
--
--   1. $\delta p$ satisfies
--   $$\begin{cases}\big[\Delta+\frac{\omega^2}{v_{\mathrm{bg}}^2}\big]\delta p=-\omega^2\,\delta m\,(\delta p+p_{\mathrm{bg}}) & \text{in }\Omega,\\[2pt] \partial_\nu\delta p-\frac{i\omega}{v}\,\delta p=i\omega\big(\frac1v-\frac1{v_{\mathrm{bg}}}\big)p_{\mathrm{bg}} & \text{on }\Gamma_{\mathrm{ABC}},\\[2pt] \delta p=0 & \text{on }\Gamma_{\mathrm{Free}}.\end{cases}$$
--   2. $\delta p$ satisfies eq. (2) as printed, with the homogeneous condition $\partial_\nu\delta p-\frac{i\omega}{v}\delta p=0$ on $\Gamma_{\mathrm{ABC}}$, if and only if $v(x)=v_{\mathrm{bg}}(x)$ or $p_{\mathrm{bg}}(x)=0$ at every point $x$ of $\Gamma_{\mathrm{ABC}}$.
--
--   This is the equation the paper derives for the residual field. Its right-hand side is the contrast source, which involves both the background field and the residual field itself.
--
--   **Formalization Note** The paper prints eq. (2) with the homogeneous absorbing condition. Subtracting the two copies of eq. (1), whose absorbing conditions have coefficients $1/v$ and $1/v_{\mathrm{bg}}$, gives the inhomogeneous condition of part 1 instead. Part 2 records exactly when the printed condition holds; the title says "(as derived)" for this reason.
--
--   The background $v_{\mathrm{bg}}$ is any positive wavespeed. The paper's $v_{\mathrm{bg}}$, obtained by a mollifying convolution of $v$, is a special case, and the derivation does not use the mollification.
--
--   The interior equation is understood at almost every point of $\Omega$, as in the definitions.
-- source:
--   Balaji, Teolis, Mis, Lara Benitez, Wang and de Hoop, Hybrid operator learning of wave scattering maps in high-contrast media, arXiv:2602.11197v1 (2026), claim c003; Section 3.2 'Scattering decomposition', eq. (2), from eq. (1) of Section 3, PDF pp. 3-4

import Mathlib
import Definitions.Def_Arxiv2602_11197_Basic

open MeasureTheory

namespace Arxiv2602_11197

theorem residual_field_equation (L₁ L₂ ω : ℝ) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hω : 0 < ω)
    (v vbg : Plane → ℝ) (hv : ∀ x ∈ closedDomain L₁ L₂, 0 < v x)
    (hvbg : ∀ x ∈ closedDomain L₁ L₂, 0 < vbg x)
    (s p pbg : Plane → ℂ) (hp : IsHelmholtzSolution L₁ L₂ ω v s p)
    (hpbg : IsHelmholtzSolution L₁ L₂ ω vbg s pbg) :
    IsResidualSolutionDerived L₁ L₂ ω v vbg pbg (p - pbg) ∧
      (IsResidualSolution L₁ L₂ ω v vbg pbg (p - pbg) ↔
        ∀ x ∈ absorbingBoundary L₁ L₂, v x = vbg x ∨ pbg x = 0) := by sorry

end Arxiv2602_11197
