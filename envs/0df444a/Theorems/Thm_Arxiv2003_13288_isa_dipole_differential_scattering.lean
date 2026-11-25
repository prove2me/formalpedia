-- Prove2me | Theorems.Thm_Arxiv2003_13288_isa_dipole_differential_scattering
-- name    : Arxiv2003_13288.isa_dipole_differential_scattering
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T08:57:37.210803+00:00
-- url     : https://prove2.me/theorems/898aa829-1b86-5133-9755-9d205c8a21a8
-- title:
--   Eq. (45): differential scattering coefficient of point dipoles under the ISA
-- statement:
--   Let $n_0>0$ and $t_0\in\mathbb C$, and take the ISA irreducible vertex of point dipoles $\Gamma(K\hat{\mathbf p},K\hat{\mathbf p}')=n_0|t_0|^2\,\mathbf I\otimes\mathbf I$ (eq. 44). Fix the incident direction $\hat{\mathbf p}'$ and an orthonormal frame $(\hat{\mathbf p}',\mathbf e_1,\mathbf e_2)$, and let $0\le\theta_s\le\pi$. Take the transverse unpolarized part of $\Gamma/(2\pi)^2$ (eqs. 41-42) and integrate it over the azimuth $\varphi_s\in[0,2\pi]$. The result is
--
--   $$\frac{d\kappa_s}{d\theta_s}=\frac{1+\cos^2\theta_s}{4\pi}\,n_0|t_0|^2.$$
--
--   **Formalization Note** The paper's next sentence, that this coefficient together with $\Sigma_{\mathrm{ISA}}=n_0t_0$ satisfies the Ward-Takahashi identity (eq. 43) for nonabsorbing scatterers, is not included (see the mission's scope).
-- source:
--   B. X. Wang and C. Y. Zhao, The dependent scattering effect on radiative properties of micro/nanoscale discrete disordered media, arXiv:2003.13288v1 (2020), claim c012; Sec. 3.2.2, eqs. (41), (42), (44), (45), PDF pp. 29-30

import Mathlib
import Definitions.Def_Arxiv2003_13288_Basic

open MeasureTheory Filter Topology

namespace Arxiv2003_13288

theorem isa_dipole_differential_scattering (n0 : ℝ) (hn0 : 0 < n0) (t0 : ℂ) (u e1 e2 : E3)
    (hframe : Orthonormal ℝ ![u, e1, e2]) (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi) :
    diffScatPolar (isaDipoleVertex n0 t0) u e1 e2 θ =
      (1 + Real.cos θ ^ 2) / (4 * Real.pi) * n0 * ‖t0‖ ^ 2 := by sorry

end Arxiv2003_13288
