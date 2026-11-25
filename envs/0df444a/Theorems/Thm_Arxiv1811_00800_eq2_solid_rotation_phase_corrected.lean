-- Prove2me | Theorems.Thm_Arxiv1811_00800_eq2_solid_rotation_phase_corrected
-- name    : Arxiv1811_00800.eq2_solid_rotation_phase_corrected
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T13:30:36.505479+00:00
-- url     : https://prove2.me/theorems/2140da1c-4698-441e-a5a6-60de8f1e4fdb
-- title:
--   Eq. (2) (corrected): the dephasing for solid rotation is $(4\pi/\lambda c)\,A$ times the vorticity $2\Omega$
-- statement:
--   Let $\lambda>0$ and $c>0$, let $\Omega\in\mathbb{R}$, and let $\gamma$ be a closed Lipschitz path in the plane with enclosed (algebraic) area $A$. For the solid-rotation flow $v=\Omega\,r\,u_\theta$:
--
--   1. the vorticity of $v$ equals $2\Omega$ at every point;
--   2. the dephasing between $\gamma$ and its counter-propagating partner is
--
--   $$\Delta\varphi=\frac{4\pi}{\lambda c}\oint_\gamma v\cdot d\ell=\frac{4\pi}{\lambda c}\,A\,(2\Omega).$$
--
--   So the dephasing is $\frac{4\pi}{\lambda c}A$ times the vorticity of the flow, and it depends on the path through $A$.
--
--   **Formalization Note** The paper prints $\Delta\varphi=\frac{4\pi}{\lambda c}A\Omega$ for the profile $v=\Omega r u_\theta$ and calls $\Omega$ "the vorticity field". With that profile the vorticity is $2\Omega$, and the printed formula is off by a factor $2$ unless $\Omega$ denotes the vorticity. The statement keeps the paper's profile and gives the correct value, which equals the printed formula with $\Omega$ read as the vorticity. $A$ is the winding-number-weighted area, the reading under which Eq. (2) holds for self-intersecting paths.
-- source:
--   Aubry and Roux, Topological Effects of a Vorticity Filament on the Coherent Backscattering Cone, arXiv:1811.00800v2 (2019), claim c019; main text, solid-rotation paragraph, Eq. (2), PDF p. 3

import Mathlib
import Definitions.Def_Arxiv1811_00800_Basic

open MeasureTheory ProbabilityTheory Complex

namespace Arxiv1811_00800

theorem eq2_solid_rotation_phase_corrected (Om lam c : ℝ) (hlam : 0 < lam) (hc : 0 < c)
    (γ : ℝ → ℂ) (hγ : IsClosedPath γ) :
    (∀ z : ℂ, vorticity (solidRotationField Om) z = 2 * Om) ∧
    phaseDiff lam c (solidRotationField Om) γ =
      4 * Real.pi / (lam * c) * enclosedArea γ * (2 * Om) := by sorry

end Arxiv1811_00800
