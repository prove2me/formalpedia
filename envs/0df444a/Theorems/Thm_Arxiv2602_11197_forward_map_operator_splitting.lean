-- Prove2me | Theorems.Thm_Arxiv2602_11197_forward_map_operator_splitting
-- name    : Arxiv2602_11197.forward_map_operator_splitting
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T20:17:44.120381+00:00
-- url     : https://prove2.me/theorems/b7d64c90-b38f-5f1c-8c52-5e8565b6e52c
-- title:
--   Section 3.2 (as derived): operator splitting of the forward map by superposition
-- statement:
--   Let $\Omega=(0,L_1)\times(0,L_2)$ with $L_1,L_2>0$, and let $\omega>0$. Let $v_{\mathrm{bg}}$ be a background wavespeed and $\delta v$ a residual, with $v_{\mathrm{bg}}>0$ and $v=v_{\mathrm{bg}}+\delta v>0$ on $\overline\Omega$. Let $s$ be a source, and let $p_{\mathrm{bg}}$ solve the Helmholtz problem (1) with wavespeed $v_{\mathrm{bg}}$ and source $s$; this is the background map $\mathcal F_{\mathrm{bg}}(s,v_{\mathrm{bg}})$. Then for every field $\delta p$:
--
--   $$\delta p\ \text{solves the residual problem for }(v,v_{\mathrm{bg}},p_{\mathrm{bg}})\iff p=\delta p+p_{\mathrm{bg}}\ \text{solves (1) with wavespeed }v\text{ and source }s.$$
--
--   Here the residual problem is
--   $$\begin{cases}\big[\Delta+\frac{\omega^2}{v_{\mathrm{bg}}^2}\big]\delta p=-\omega^2\,\delta m\,(\delta p+p_{\mathrm{bg}}) & \text{in }\Omega,\\[2pt] \partial_\nu\delta p-\frac{i\omega}{v}\,\delta p=i\omega\big(\frac1v-\frac1{v_{\mathrm{bg}}}\big)p_{\mathrm{bg}} & \text{on }\Gamma_{\mathrm{ABC}},\\[2pt] \delta p=0 & \text{on }\Gamma_{\mathrm{Free}},\end{cases}$$
--   with $\delta m=(v_{\mathrm{bg}}+\delta v)^{-2}-v_{\mathrm{bg}}^{-2}$.
--
--   So the solutions of the full problem with wavespeed $v$ are exactly the superpositions $\delta p+p_{\mathrm{bg}}$ of the background field and a solution of the scattering-corrector problem. This is the operator splitting $\mathcal F(s,v)=\mathcal F_{\mathrm{bg}}(s,v_{\mathrm{bg}})+\mathcal F_{\mathrm{sc}}(p_{\mathrm{bg}},\delta v)$ of Section 3.2.
--
--   **Formalization Note** The paper does not discuss existence or uniqueness of solutions, so the maps $\mathcal F$, $\mathcal F_{\mathrm{bg}}$ and $\mathcal F_{\mathrm{sc}}$ are not formed as functions. The splitting is stated as the equivalence above, between solutions of the two problems. Wherever the problems are uniquely solvable, it gives the identity of solution maps.
--
--   The paper writes $\mathcal F_{\mathrm{sc}}$ as a function of $(p_{\mathrm{bg}},\delta v)$ and says it suppresses the dependence on $v_{\mathrm{bg}}$. The residual problem involves $v_{\mathrm{bg}}$ in its operator, in $\delta m$ and in the absorbing condition, so $v_{\mathrm{bg}}$ appears explicitly here.
--
--   The residual problem uses the absorbing condition obtained by subtraction (see the residual field equation, eq. (2)). With the homogeneous condition printed in eq. (2), the equivalence fails wherever $v\ne v_{\mathrm{bg}}$ and $p_{\mathrm{bg}}\ne0$ on $\Gamma_{\mathrm{ABC}}$; the title says "(as derived)" for this reason.
--
--   The background $v_{\mathrm{bg}}$ is any positive wavespeed, which includes the paper's mollified one.
-- source:
--   Balaji, Teolis, Mis, Lara Benitez, Wang and de Hoop, Hybrid operator learning of wave scattering maps in high-contrast media, arXiv:2602.11197v1 (2026), claim c004; Section 3.2 'Scattering decomposition', maps F_bg and F_sc and the superposition p = δp + p_bg, PDF p. 4

import Mathlib
import Definitions.Def_Arxiv2602_11197_Basic

open MeasureTheory

namespace Arxiv2602_11197

theorem forward_map_operator_splitting (L₁ L₂ ω : ℝ) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hω : 0 < ω)
    (vbg dv : Plane → ℝ) (hvbg : ∀ x ∈ closedDomain L₁ L₂, 0 < vbg x)
    (hv : ∀ x ∈ closedDomain L₁ L₂, 0 < vbg x + dv x)
    (s pbg : Plane → ℂ) (hpbg : IsHelmholtzSolution L₁ L₂ ω vbg s pbg) (dp : Plane → ℂ) :
    IsResidualSolutionDerived L₁ L₂ ω (vbg + dv) vbg pbg dp ↔
      IsHelmholtzSolution L₁ L₂ ω (vbg + dv) s (dp + pbg) := by sorry

end Arxiv2602_11197
