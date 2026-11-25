-- Prove2me | Theorems.Thm_Arxiv2105_07250_moving_source_pressure_A14
-- name    : Arxiv2105_07250.moving_source_pressure_A14
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T09:30:19.447197+00:00
-- url     : https://prove2.me/theorems/dcb796c9-2132-464a-bb15-6635011997bc
-- title:
--   Eq. (A14) (as proved): the pressure field obtained from the potential (A12)
-- statement:
--   Let $\rho,c,\tilde\omega>0$. Let the receiver be $x=(0,x_y)$ with $x_y\neq0$, and let the source velocity be $v=(v_x,0)$ (in Lean, `v 1 = 0`: the first, 0-indexed coordinate is the free one) with $|v|<c$. Put $M=|v|/c$ and $t_x=|x|/c$, and let $\phi(t,x,v)$ be the potential of eq. (A12) as printed. Then $p=\rho\,\mathrm{Re}\,\partial_t\phi$ (eq. A3) equals the expression of eq. (A14) for every $t$:
--
--   $$\rho\,\mathrm{Re}\,\partial_t\phi(t,x,v)=\mathrm{Re}\Big\{-\frac{i\rho\tilde\omega}{4c^2(1-M^2)^{3/2}}e^{-i\frac{\tilde\omega}{1-M^2}t}\Big[\frac{M^2t}{R}\mathcal H_1^{(1)}\Big(\frac{\tilde\omega R}{1-M^2}\Big)+i\,\mathcal H_0^{(1)}\Big(\frac{\tilde\omega R}{1-M^2}\Big)\Big]\Big\},$$
--
--   where $R=\sqrt{M^2t^2+(1-M^2)t_x^2}$.
--
--   **Formalization Note** The claim that (A12) solves the wave equation (A4) is not included: at $v=0$, (A12) differs from the field given by (A7) by a factor $c^{-2}$ (see REPORT.md). What the paper derives in (A13)-(A14) is the computation of $\rho\,\mathrm{Re}\,\partial_t$ of (A12) in this geometry, and that computation is what is stated. $x_y\ne0$ (the receiver is off the source line) keeps the Hankel argument positive.
-- source:
--   D. Ayala-Garcia, A. Curtis and M. Branicki, Seismic Interferometry from Correlated Noise Sources, arXiv:2105.07250v2 (2021), claim c024; Appendix A, eqs. (A3), (A12)-(A14), PDF pp. 32-34

import Mathlib
import Definitions.Def_Arxiv2105_07250_Basic

open MeasureTheory ProbabilityTheory Filter Topology

namespace Arxiv2105_07250

theorem moving_source_pressure_A14 (ρ c wt : ℝ) (hρ : 0 < ρ) (hc : 0 < c) (hwt : 0 < wt)
    (x v : Plane) (hx0 : x 0 = 0) (hx : x ≠ 0) (hv1 : v 1 = 0) (hv : ‖v‖ < c) (t : ℝ) :
    ρ * (deriv (fun s : ℝ => potentialA12 c wt s x v) t).re =
      pressureA14 ρ c wt (‖v‖ / c) (‖x‖ / c) t := by sorry

end Arxiv2105_07250
