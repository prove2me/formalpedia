-- Prove2me | Theorems.Thm_Arxiv2003_13288_qca_dipole_self_energy
-- name    : Arxiv2003_13288.qca_dipole_self_energy
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T09:07:09.500082+00:00
-- url     : https://prove2.me/theorems/56376f2d-989c-5110-9eda-c3a65b74a21d
-- title:
--   Eqs. (79)-(80): the QCA self-energy of electric dipoles and its Lorenz-Lorentz limit
-- statement:
--   Let $n_0,k>0$ and $t_0\in\mathbb C$. Let $h_2=g_2-1$ be a measurable pair correlation function with $h_2\ge-1$ and $\int_0^\infty r|h_2(r)|\,dr<\infty$. Write $c=\int_0^\infty dr\,r\,e^{ikr}[g_2(r)-1]$. Then:
--
--   1. the principal-value integral of the regular part of the Green's function (eqs. 73-74) exists and is isotropic:
--   $$\int d^3\mathbf r\;\mathrm{PV}\,\mathbf G_0(\mathbf r)\,h_2(r)=-\frac23\,c\;\mathbf I;$$
--   2. a scalar $\Sigma$ solves the local QCA equation (79)
--   $$\Sigma\mathbf I=n_0t_0\mathbf I-\frac{n_0t_0\Sigma}{3k^2}\mathbf I+n_0t_0\Sigma\int d^3\mathbf r\;\mathrm{PV}\,\mathbf G_0(\mathbf r)h_2(r)$$
--   if and only if $1+n_0t_0/(3k^2)+\tfrac23n_0t_0c\ne0$ and
--   $$\Sigma=\frac{n_0t_0}{1+n_0t_0/(3k^2)+2n_0t_0\int_0^\infty dr\,r\,e^{ikr}[g_2(r)-1]/3}\qquad\text{(eq. 80)};$$
--   3. (point-scatterer limit) let $H$ be a measurable function with $\int_0^\infty x|H(x)|\,dx<\infty$, and let the pair correlation function of particles of radius $a>0$ be $h_2^{(a)}(r)=H(r/a)$, i.e. its shape scales with the particle size (the hard-sphere exclusion hole $h_2^{(a)}=-1$ for $r<2a$ and $0$ otherwise is the case $H=-\mathbf 1_{[0,2)}$). If $1+n_0t_0/(3k^2)\ne0$, then as $a\to0^+$ the QCA self-energy (eq. 80) with $h_2^{(a)}$ tends to the Lorenz-Lorentz self-energy $\Sigma_{\mathrm{LLR}}=n_0t_0/(1+n_0t_0/(3k^2))$ (eq. 65).
--
--   **Formalization Note** $\mathrm{PV}\,\mathbf G_0$ is built from the components of eqs. (73)-(74). With the real-space Green's function of eq. (53), which has the opposite sign, item 1 would read $+\tfrac23c\,\mathbf I$ and eq. (80) would have a minus sign before its correlation term. In item 3 the paper does not say how $h_2$ depends on $a$; the statement takes correlations whose length scale is proportional to $a$, and the vanishing of the correlation integral is part of what must be proved. The number density $n_0$ and the T-operator $t_0$ are held fixed in the limit.
-- source:
--   B. X. Wang and C. Y. Zhao, The dependent scattering effect on radiative properties of micro/nanoscale discrete disordered media, arXiv:2003.13288v1 (2020), claim c007; Sec. 4.2.4, eqs. (73), (74), (79), (80), and eq. (65), PDF pp. 52, 54-55

import Mathlib
import Definitions.Def_Arxiv2003_13288_Basic

open MeasureTheory Filter Topology

namespace Arxiv2003_13288

theorem qca_dipole_self_energy (n0 k : ℝ) (hn0 : 0 < n0) (hk : 0 < k) (t0 : ℂ) (h2 : ℝ → ℝ)
    (hmeas : Measurable h2) (hint : IntegrableOn (fun r => r * h2 r) (Set.Ioi 0))
    (hg2 : ∀ r, -1 ≤ h2 r) :
    Tendsto (pvTrunc k h2) (𝓝[>] 0)
      (𝓝 ((-(2 / 3) * corrIntegral k h2) • (1 : Matrix (Fin 3) (Fin 3) ℂ))) ∧
    (∀ Sig : ℂ,
      Sig • (1 : Matrix (Fin 3) (Fin 3) ℂ) =
          ((n0 : ℂ) * t0) • (1 : Matrix (Fin 3) (Fin 3) ℂ) -
            ((n0 : ℂ) * t0 * Sig / (3 * (k : ℂ) ^ 2)) • (1 : Matrix (Fin 3) (Fin 3) ℂ) +
            ((n0 : ℂ) * t0 * Sig) • pvGreenIntegral k h2 ↔
        (1 + n0 * t0 / (3 * (k : ℂ) ^ 2) + 2 * n0 * t0 * corrIntegral k h2 / 3 ≠ 0 ∧
          Sig = qcaSelfEnergy n0 k t0 h2)) ∧
    (∀ H : ℝ → ℝ, Measurable H → IntegrableOn (fun x => x * H x) (Set.Ioi 0) →
      1 + n0 * t0 / (3 * (k : ℂ) ^ 2) ≠ 0 →
      Tendsto (fun a : ℝ => qcaSelfEnergy n0 k t0 (fun r => H (r / a))) (𝓝[>] 0)
        (𝓝 (llrSelfEnergy n0 k t0))) := by sorry

end Arxiv2003_13288
