-- Prove2me | Theorems.Thm_Arxiv1801_00461_model_apparent_conductivity_deviation
-- name    : Arxiv1801_00461.model_apparent_conductivity_deviation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:15:18.485488+00:00
-- url     : https://prove2.me/theorems/39c9be7d-23e6-4d20-b02e-6e7f704f44d1
-- title:
--   Eqs. (39)-(40) (as proved): the apparent conductivity of the model $\varepsilon_A=\varepsilon_o+\kappa/|\omega|^{2+x}$
-- statement:
--   Let $\varepsilon_o>0$, $\kappa\ge0$ and $-1<x<1$, and consider the apparent permittivity $\varepsilon_A(\omega)=\varepsilon_o+\kappa/|\omega|^{2+x}$ (eq. (38)). Then the principal value
--
--   $$⨍_0^\infty\frac{dy}{(y^2-1)y^x}=\lim_{\delta\to0^+}\Big[\int_\delta^{1-\delta}+\int_{1+\delta}^{1/\delta}\Big]\frac{dy}{(y^2-1)y^x}$$
--
--   exists. With $\kappa_1=\frac{2\kappa}\pi⨍_0^\infty\frac{dy}{(y^2-1)y^x}$ (eq. (40)), for every $\omega>0$
--
--   $$\mathcal H\big(\bar\Delta(\omega\varepsilon_A)\big)(\omega)=\frac{2\kappa}{\pi\omega^{1+x}}⨍_0^\infty\frac{dy}{(y^2-1)y^x}=\frac{\kappa_1}{\omega^{1+x}},$$
--
--   so that by eq. (30b) $\bar\Delta\sigma_A(\omega)=-\kappa_1/\omega^{1+x}$ (eq. (39)).
--
--   **Formalization Note** The paper states the model for $x\ge-1$. The principal value converges at $y\to\infty$ only for $x>-1$ and at $y\to0$ only for $x<1$, so the statement is for $-1<x<1$, which is the range in which the paper's computation is valid.
-- source:
--   Bédard and Destexhe, Kramers-Kronig relations and the properties of conductivity and permittivity in heterogeneous media, arXiv:1801.00461v1 (2018), claim c016; Sec. 3.1.2, eqs. (38)-(40) and (42), PDF p. 13

import Mathlib
import Definitions.Def_Arxiv1801_00461_Basic

open MeasureTheory Filter Topology

namespace Arxiv1801_00461

theorem model_apparent_conductivity_deviation (eps0 kappa x : ℝ) (heps0 : 0 < eps0)
    (hkappa : 0 ≤ kappa) (hx1 : -1 < x) (hx2 : x < 1) :
    (∃ P : ℝ, Tendsto (kernelTrunc x) (𝓝[>] 0) (𝓝 P)) ∧
    ∀ ω : ℝ, 0 < ω →
      HasHilbert (omegaEpsDev eps0 kappa x) ω (kappaOne kappa x / ω ^ (1 + x)) := by sorry

end Arxiv1801_00461
