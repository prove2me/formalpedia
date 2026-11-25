-- Prove2me | Theorems.Thm_Arxiv2003_13288_qca_differential_scattering
-- name    : Arxiv2003_13288.qca_differential_scattering
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T09:06:48.55702+00:00
-- url     : https://prove2.me/theorems/5bc49579-eeb0-4496-8095-852b9d7e67c6
-- title:
--   Eq. (84): differential scattering coefficient under the QCA
-- statement:
--   Let $n_0,k,K>0$ and $t_0\in\mathbb C$. Let $h_2=g_2-1$ be a measurable pair correlation function with $h_2\ge-1$, $\int_0^\infty r|h_2(r)|\,dr<\infty$ and $\int d^3\mathbf r\,|h_2(r)|<\infty$, and let $H_2$ be its Fourier transform (eq. 78). Let $C=\Sigma_{\mathrm{QCA}}/n_0$ with $\Sigma_{\mathrm{QCA}}$ the self-energy of eq. (80). Take the on-shell QCA vertex $\Gamma(K\hat{\mathbf p},K\hat{\mathbf p}')=[n_0|C|^2+n_0^2|C|^2H_2(K\hat{\mathbf p}-K\hat{\mathbf p}')]\,\mathbf I\otimes\mathbf I$ (eq. 83). Fix the incident direction $\hat{\mathbf p}'$ and an orthonormal frame $(\hat{\mathbf p}',\mathbf e_1,\mathbf e_2)$, and let $0\le\theta_s\le\pi$. Take the transverse unpolarized part of $\Gamma/(2\pi)^2$ (eqs. 41-42) and integrate it over the azimuth $\varphi_s\in[0,2\pi]$. The result is
--
--   $$\frac{d\kappa_s}{d\theta_s}=\frac{n_0|C|^2(1+\cos^2\theta_s)}{4\pi}\Big\{1+n_0H_2\big[2K\sin(\theta_s/2)\big]\Big\},$$
--
--   where $H_2[q]$ denotes the value of $H_2$ at any vector of length $q$; the Lean statement uses $q\,\hat{\mathbf p}'$.
--
--   **Formalization Note** The on-shell momentum $K$ is taken real and positive, so that $K\hat{\mathbf p}-K\hat{\mathbf p}'$ is a real momentum transfer of length $2K\sin(\theta_s/2)$.
-- source:
--   B. X. Wang and C. Y. Zhao, The dependent scattering effect on radiative properties of micro/nanoscale discrete disordered media, arXiv:2003.13288v1 (2020), claim c009; Sec. 4.2.4, eqs. (42), (78), (80), (82)-(84), PDF pp. 54-55

import Mathlib
import Definitions.Def_Arxiv2003_13288_Basic

open MeasureTheory Filter Topology

namespace Arxiv2003_13288

theorem qca_differential_scattering (n0 k K : ℝ) (hn0 : 0 < n0) (hk : 0 < k) (hK : 0 < K)
    (t0 : ℂ) (h2 : ℝ → ℝ) (hmeas : Measurable h2) (hint : IntegrableOn (fun r => r * h2 r) (Set.Ioi 0))
    (hint3 : Integrable (fun r : E3 => h2 ‖r‖)) (hg2 : ∀ r, -1 ≤ h2 r)
    (C : ℂ) (hC : C = qcaSelfEnergy n0 k t0 h2 / n0) (u e1 e2 : E3)
    (hframe : Orthonormal ℝ ![u, e1, e2]) (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi) :
    diffScatPolar (qcaVertex n0 K C h2) u e1 e2 θ =
      n0 * ‖C‖ ^ 2 * (1 + Real.cos θ ^ 2) / (4 * Real.pi) *
        (1 + n0 * pairCorrFT h2 ((2 * K * Real.sin (θ / 2)) • u)) := by sorry

end Arxiv2003_13288
