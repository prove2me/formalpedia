-- Prove2me | Theorems.Thm_CondMat0408017_primary_field_boundary_conditions
-- name    : CondMat0408017.primary_field_boundary_conditions
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-26T13:18:26.604253+00:00
-- url     : https://prove2.me/theorems/109f18d0-70f7-4e15-b1fb-f0dbbf39fa37
-- title:
--   Eqs. (Elmag:BCS): boundary conditions on the primary field at a one-dimensional interface
-- statement:
--   Let $x_3=\zeta(x_1)$ be an interface between two media, and fix a point of it where $\zeta'(x_1)=\zeta'$. Let $\omega\ne0$, and let $\kappa^\pm\ne0$ be the material constants of the two media ($\kappa=\varepsilon$ for $p$, $\kappa=\mu$ for $s$). Let $\Phi^\pm,\partial_1\Phi^\pm,\partial_3\Phi^\pm$ be the values at the point of the primary field on the two sides ($\Phi_p=H_2$, $\Phi_s=E_2$), and let $E^\pm,H^\pm$ be the fields they determine through (Elmag:BS:p-pol), (Elmag:BS:s-pol). Then the Maxwell conditions without surface charge and current,
--
--   $$n\times(E^--E^+)=0,\qquad n\times(H^--H^+)=0,$$
--
--   with $n$ the unit normal, hold if and only if
--
--   $$\Phi^+=\Phi^-,\qquad \frac{1}{\kappa^+}\partial_n\Phi^+=\frac{1}{\kappa^-}\partial_n\Phi^-,\qquad \partial_n=\frac{-\zeta'\partial_{x_1}+\partial_{x_3}}{\sqrt{1+\zeta'^2}} .$$
--
--   These are the boundary conditions (Elmag:BCS) on the primary field.
--
--   **Formalization Note** The normal is $n=(-\zeta',0,1)/\sqrt{1+\zeta'^2}$, for which $n\cdot\nabla=\partial_n$. The paper prints $(\zeta'e_1+e_3)/\sqrt{1+\zeta'^2}$, a sign slip. Only the tangential conditions (Elmag:BC3), (Elmag:BC4) are imposed: for these fields the paper's derivation uses only them, and the normal conditions add no constraint.
-- source:
--   I. Simonsen, A random walk through surface scattering phenomena: Theory and phenomenology, arXiv:cond-mat/0408017v1 (2004), claim c045; Sec. II.C.1, eqs. (Elmag:BCSa)-(Elmag:BCSc) from (Elmag:BC3)-(Elmag:BC4), (Elmag:BS:p-pol), (Elmag:BS:s-pol), PDF p. 8

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex

namespace CondMat0408017

theorem primary_field_boundary_conditions (ν : Polarization) (ω : ℝ) (hω : ω ≠ 0)
    (κP κM : ℂ) (hκP : κP ≠ 0) (hκM : κM ≠ 0) (dζ : ℝ) (ΦP d1P d3P ΦM d1M d3M : ℂ) :
    (crossProduct (surfaceNormal dζ)
          ((emFields ν ω κM ΦM d1M d3M).1 - (emFields ν ω κP ΦP d1P d3P).1) = 0 ∧
        crossProduct (surfaceNormal dζ)
          ((emFields ν ω κM ΦM d1M d3M).2 - (emFields ν ω κP ΦP d1P d3P).2) = 0) ↔
      (ΦP = ΦM ∧ normalDeriv dζ d1P d3P / κP = normalDeriv dζ d1M d3M / κM) := by sorry

end CondMat0408017
