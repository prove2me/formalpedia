-- Prove2me | Theorems.Thm_Arxiv2001_06227_single_scattering_reflection_transmission
-- name    : Arxiv2001_06227.single_scattering_reflection_transmission
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T08:28:03.018709+00:00
-- url     : https://prove2.me/theorems/bff935b8-3ea3-542c-9fca-0d37a3376f6c
-- title:
--   Eq. (D3) (as corrected): $R+T$ of the slab in the single-scattering approximation
-- statement:
--   Let $p(\mu,\mu')$ be the azimuth-integrated phase function, with $\mu\mapsto p(\mu,1)$ non-negative and integrable on $[-1,1]$ with integral $1$. Let $\mu_s,\mu_a,L>0$ and $\mu_e=\mu_a+\mu_s$. Define the single-scattering reflection
--
--   $$R=\int_0^\infty\!\mu_se^{-\mu_ss}\!\int_{-1}^0\!p(\mu,1)\!\int_0^\infty\!\mu_se^{-\mu_ss'}e^{-\mu_a(s-s/\mu)}\,\Theta[L-s]\,\Theta[s'+s/\mu]\,ds'\,d\mu\,ds$$
--
--   and transmission
--
--   $$T=e^{-\mu_eL}+\int_0^\infty\!\mu_se^{-\mu_ss}\!\int_{0}^1\!p(\mu,1)\!\int_0^\infty\!\mu_se^{-\mu_ss'}e^{-\mu_a(s+(L-s)/\mu)}\,\Theta[L-s]\,\Theta[s'-(L-s)/\mu]\,ds'\,d\mu\,ds.$$
--
--   Then
--
--   $$R+T=e^{-\mu_eL}+\int_0^1\frac{\mu_s}{\mu_e}\frac{\mu}{\mu+1}p(-\mu,1)\Big\{1-e^{-\mu_eL\frac{\mu+1}{\mu}}\Big\}d\mu+\int_0^1\frac{\mu_s}{\mu_e}\frac{\mu}{\mu-1}p(\mu,1)\Big\{1-e^{-\mu_eL\frac{\mu-1}{\mu}}\Big\}e^{-\mu_eL/\mu}d\mu.$$
--
--   **Formalization Note** In $T$ the $\mu$-integral runs over $(0,1)$; the paper prints $\int_{\mu=-1}^0$ in (D2), with which the integral diverges and (D3) does not follow. The $\mu$-integrals in (D3) are taken over the open interval $(0,1)$, so the removable singularity of the last integrand at $\mu=1$ is never evaluated; the endpoints do not affect the integral.
-- source:
--   Sheremet, Pierrat and Carminati, Absorption of scalar waves in correlated disordered media and its maximization using stealth hyperuniformity, arXiv:2001.06227v2 (2020), claim c029; Appendix D, eqs. (D1)-(D3), PDF p. 12

import Mathlib
import Definitions.Def_Arxiv2001_06227_Basic

open MeasureTheory Filter Topology

namespace Arxiv2001_06227

theorem single_scattering_reflection_transmission (p : ℝ → ℝ → ℝ) (hp : IsAzimuthalPhase p)
    (muS muA L : ℝ) (hmuS : 0 < muS) (hmuA : 0 < muA) (hL : 0 < L) :
    slabReflect p muS muA L + slabTransmit p muS muA L = slabRT p muS muA L := by sorry

end Arxiv2001_06227
