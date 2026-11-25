-- Prove2me | Theorems.Thm_Arxiv1811_00800_eq4_vortex_phase_topological
-- name    : Arxiv1811_00800.eq4_vortex_phase_topological
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T20:44:43.194845+00:00
-- url     : https://prove2.me/theorems/89783d5d-4cc9-51da-9f71-3c8d8fe2f330
-- title:
--   Eq. (4): around a vorticity filament the dephasing is $4\pi\alpha n$, with $n$ the number of loops
-- statement:
--   Let $\lambda>0$, $c>0$, $\Gamma\in\mathbb{R}$, and $\alpha=\Gamma/(\lambda c)$. Let $\gamma$ be a closed Lipschitz path that does not pass through the vorticity filament at the origin, and let the flow be $v=\frac{\Gamma}{2\pi r}u_\theta$. Then the number of loops of $\gamma$ around the filament is an integer $n$, and the dephasing between $\gamma$ and its counter-propagating partner is
--
--   $$\Delta\varphi=\frac{4\pi}{\lambda c}\,n\,\Gamma=4\pi\alpha\, n.$$
--
--   The dephasing depends only on the discrete number of loops and not on the shape of the path: this is the topological stability that the paper compares to the Aharonov-Bohm effect.
--
--   **Formalization Note** The filament is a point vortex at the origin and the paths only have to avoid that point; the paper's condition that paths stay outside the core gives the same values, since $\Delta\varphi$ depends only on the flow along the path. $n$ is the signed winding number given by the Cauchy integral.
-- source:
--   Aubry and Roux, Topological Effects of a Vorticity Filament on the Coherent Backscattering Cone, arXiv:1811.00800v2 (2019), claim c016; main text, vorticity-filament paragraph, Eq. (4), PDF p. 4

import Mathlib
import Definitions.Def_Arxiv1811_00800_Basic

open MeasureTheory ProbabilityTheory Complex

namespace Arxiv1811_00800

theorem eq4_vortex_phase_topological (Gam lam c : ℝ) (hlam : 0 < lam) (hc : 0 < c)
    (γ : ℝ → ℂ) (hγ : IsClosedPath γ) (h0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ≠ 0) :
    ∃ n : ℤ, windingNumber γ 0 = n ∧
      phaseDiff lam c (vortexField Gam) γ = 4 * Real.pi / (lam * c) * n * Gam ∧
      phaseDiff lam c (vortexField Gam) γ = 4 * Real.pi * abParam Gam lam c * n := by sorry

end Arxiv1811_00800
