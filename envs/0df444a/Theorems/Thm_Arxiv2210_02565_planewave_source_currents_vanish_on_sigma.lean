-- Prove2me | Theorems.Thm_Arxiv2210_02565_planewave_source_currents_vanish_on_sigma
-- name    : Arxiv2210_02565.planewave_source_currents_vanish_on_sigma
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T12:51:02.633512+00:00
-- url     : https://prove2.me/theorems/95867c41-96d4-4354-a799-d75e8e933fbf
-- title:
--   Sec. III, eq. (7): the planewave source currents vanish on $\Sigma$
-- statement:
--   Let a planewave $\mathbf E^{\rm inc}=(\mathbf p\times\mathbf k)e^{i\mathbf k\cdot\mathbf r}$ with $\mathbf k=(0,k_{1y},-k_{1z})$, $k_{1y},k_{1z}\in\mathbb R$, $k_{1z}\ge0$, $k_{1y}^2+k_{1z}^2=k_1^2=\omega^2\mu_1\epsilon_1$, $\omega>0$, impinge from $D_1=\{z>0\}$ on the flat interface $\Sigma=\{z=0\}$ with the medium $(\epsilon_2,\mu_2)$ below. Assume $\epsilon_1,\mu_1,\epsilon_2,\mu_2\ne0$ and that the Fresnel denominators $\mu_2k_{1z}+\mu_1k_{2z}$ and $\epsilon_2k_{1z}+\epsilon_1k_{2z}$ are nonzero. Let $(\mathbf E^{\rm src},\mathbf H^{\rm src})$ be the source field (7): incident plus reflected field in $\Omega_1$ and transmitted field in $\Omega_2$. Then at every point $\mathbf r\in\Sigma$, with $\hat{\mathbf n}=\hat{\mathbf z}$,
--
--   $$\mathbf M^{\rm src}(\mathbf r)=\hat{\mathbf z}\times\big(\mathbf E^{\rm src}|_+-\mathbf E^{\rm src}|_-\big)(\mathbf r)=\mathbf 0,\qquad \mathbf J^{\rm src}(\mathbf r)=\hat{\mathbf z}\times\big(\mathbf H^{\rm src}|_+-\mathbf H^{\rm src}|_-\big)(\mathbf r)=\mathbf 0.$$
--
--   So the source field satisfies the exact transmission conditions on $\Sigma$, and the source currents of the integral equation (18) are supported on the local perturbation $\Gamma\setminus\Sigma$.
--
--   **Formalization Note** The two expressions in (7) are smooth on all of $\mathbb R^3$, so the one-sided limits in (5) are the values of the $\Omega_1$ and $\Omega_2$ expressions at $\mathbf r$. The nonvanishing of $\epsilon_j,\mu_j$ and of the Fresnel denominators is implicit in the paper, which divides by them.
-- source:
--   Arrieta and Pérez-Arancibia, Windowed Green Function MoM for Second-Kind Surface Integral Equation Formulations of Layered Media Electromagnetic Scattering Problems, arXiv:2210.02565v1 (2022), claim c001; Section III (Incident and source fields), eqs. (5)-(7) and the sentence after eq. (7), PDF p. 3

import Mathlib
import Definitions.Def_Arxiv2210_02565_Basic

open Filter Topology

namespace Arxiv2210_02565

theorem planewave_source_currents_vanish_on_sigma (s : PlanewaveSetup) (hω : 0 < s.ω)
    (hε1 : s.ε1 ≠ 0) (hμ1 : s.μ1 ≠ 0) (hε2 : s.ε2 ≠ 0) (hμ2 : s.μ2 ≠ 0)
    (hk1z : 0 ≤ s.k1z) (hk1 : (s.k1y : ℂ) ^ 2 + (s.k1z : ℂ) ^ 2 = (s.ω : ℂ) ^ 2 * s.μ1 * s.ε1)
    (hTE : s.μ2 * s.k1z + s.μ1 * s.k2z ≠ 0) (hTM : s.ε2 * s.k1z + s.ε1 * s.k2z ≠ 0) :
    ∀ r : Space, r 2 = 0 → srcCurrentM s zhat r = 0 ∧ srcCurrentJ s zhat r = 0 := by sorry

end Arxiv2210_02565
