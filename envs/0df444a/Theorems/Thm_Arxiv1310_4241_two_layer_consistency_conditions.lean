-- Prove2me | Theorems.Thm_Arxiv1310_4241_two_layer_consistency_conditions
-- name    : Arxiv1310_4241.two_layer_consistency_conditions
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T11:25:42.026235+00:00
-- url     : https://prove2.me/theorems/8de5f0dc-eb01-4903-90de-f0c2f47e6101
-- title:
--   Eq. (49): the consistency conditions $\nabla\cdot\mathbf j_j=ik_jr_j$, $\nabla\cdot\mathbf m_j=ik_jq_j$ for the two-layer currents (48)
-- statement:
--   Let $\omega>0$, let $\varepsilon_0,\mu_0,\varepsilon_1,\mu_1>0$, $k_j=\omega\sqrt{\varepsilon_j\mu_j}$, and let $(\xi,\eta)\ne(0,0)$. For the densities $r_j=\widehat r_je^{i(\xi x+\eta y)}$, $q_j=\widehat q_je^{i(\xi x+\eta y)}$ on $z=0$, let the currents be
--
--   $$\mathbf j_0=i\omega\Big(\sqrt{\mu_0\varepsilon_0}\,\nabla\triangle^{-1}r_0-\varepsilon_1\sqrt{\tfrac{\mu_1}{\varepsilon_0}}\,\mathbf n\times\nabla\triangle^{-1}r_1\Big),\qquad \mathbf j_1=\mathbf n\times\sqrt{\tfrac{\varepsilon_0}{\varepsilon_1}}\,\mathbf j_0,$$
--
--   $$\mathbf m_0=i\omega\Big(\sqrt{\mu_0\varepsilon_0}\,\nabla\triangle^{-1}q_0-\mu_1\sqrt{\tfrac{\varepsilon_1}{\mu_0}}\,\mathbf n\times\nabla\triangle^{-1}q_1\Big),\qquad \mathbf m_1=\mathbf n\times\sqrt{\tfrac{\mu_0}{\mu_1}}\,\mathbf m_0$$
--
--   (eq. (48)). Then
--
--   $$\nabla\cdot\mathbf j_j=ik_jr_j,\qquad \nabla\cdot\mathbf m_j=ik_jq_j\qquad(j=0,1).$$
--
--   **Formalization Note** Eq. (49) prints $ik$ without the layer index; the wavenumber of layer $j$ is $k_j$. The statement is for one Fourier mode, on which $\triangle^{-1}$ is multiplication by $-1/(\xi^2+\eta^2)$ (eq. (41)); the divergence is the true planar divergence of the current.
-- source:
--   M. O'Neil, A generalized Debye source approach to electromagnetic scattering in layered media, arXiv:1310.4241v1 (2013), claim c020; Section V.B, eqs. (48) and (49), PDF pp. 11-12

import Mathlib
import Definitions.Def_Arxiv1310_4241_Basic

open MeasureTheory Filter Topology

namespace Arxiv1310_4241

theorem two_layer_consistency_conditions (ω ε0 μ0 ε1 μ1 : ℝ) (hω : 0 < ω) (hε0 : 0 < ε0)
    (hμ0 : 0 < μ0) (hε1 : 0 < ε1) (hμ1 : 0 < μ1) (ξ η : ℝ) (hξη : (ξ, η) ≠ (0, 0))
    (r0 r1 q0 q1 : ℂ) (p : Space) :
    tangentialDivergence (modeField (twoLayerJ0 ω ε0 μ0 ε1 μ1 ξ η r0 r1) ξ η) p =
        Complex.I * wavenumber ω ε0 μ0 * (r0 * mode ξ η p) ∧
    tangentialDivergence (modeField (twoLayerJ1 ω ε0 μ0 ε1 μ1 ξ η r0 r1) ξ η) p =
        Complex.I * wavenumber ω ε1 μ1 * (r1 * mode ξ η p) ∧
    tangentialDivergence (modeField (twoLayerM0 ω ε0 μ0 ε1 μ1 ξ η q0 q1) ξ η) p =
        Complex.I * wavenumber ω ε0 μ0 * (q0 * mode ξ η p) ∧
    tangentialDivergence (modeField (twoLayerM1 ω ε0 μ0 ε1 μ1 ξ η q0 q1) ξ η) p =
        Complex.I * wavenumber ω ε1 μ1 * (q1 * mode ξ η p) := by sorry

end Arxiv1310_4241
