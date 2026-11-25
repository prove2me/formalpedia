-- Prove2me | Theorems.Thm_Arxiv1110_5134_stokes_Q_transport
-- name    : Arxiv1110_5134.stokes_Q_transport
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T09:01:24.180358+00:00
-- url     : https://prove2.me/theorems/5fe730db-fe37-451d-b00f-5335b3afa525
-- title:
--   Eqs. (9)-(11): transport law for $Q/n^2$
-- statement:
--   Along a ray with arc length $s$ and refractive index $n(s)>0$, suppose $\frac{d}{ds}[I/n^2]=0$ (Eq. 3), $d\chi/ds=0$ (conservation of the ellipticity angle), and Rytov's law $d\psi/ds=\kappa$ (Eq. 2), where $\kappa$ is the torsion of the ray. Then (Eq. 10)
--
--   $$\frac{d}{ds}\Big[\frac{I\cos2\chi}{n^2}\Big]=0,$$
--
--   and the second Stokes component $Q=I\cos2\chi\cos2\psi$ satisfies (Eqs. 9, 11)
--
--   $$\frac{d}{ds}\Big[\frac{Q}{n^2}\Big]=-\sin2\psi\,\frac{d(2\psi)}{ds}\,\frac{I\cos2\chi}{n^2}=-2\kappa\frac{U}{n^2},$$
--
--   where $U=I\cos2\chi\sin2\psi$.
--
--   **Formalization Note** The statement is at a single point $s$ of the ray, with $\kappa$ the value of the torsion there.
-- source:
--   Zhao, Tan and Liu, On the Derivation of Vector Radiative Transfer Equation for Polarized Radiative Transport in Graded Index Media, arXiv:1110.5134v1 (2011), claim c003; Section 3.1, Eqs. (9)-(11), PDF pp. 9-10

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic

open MeasureTheory Filter Topology
open scoped Matrix

namespace Arxiv1110_5134

theorem stokes_Q_transport (n I χ ψ : ℝ → ℝ) (κ s : ℝ) (hn : 0 < n s)
    (hI : HasDerivAt (fun t => I t / n t ^ 2) 0 s) (hχ : HasDerivAt χ 0 s)
    (hψ : HasDerivAt ψ κ s) :
    HasDerivAt (fun t => I t * Real.cos (2 * χ t) / n t ^ 2) 0 s ∧
    HasDerivAt (fun t => stokesVec (I t) (χ t) (ψ t) 1 / n t ^ 2)
      (-Real.sin (2 * ψ s) * (2 * κ) * (I s * Real.cos (2 * χ s) / n s ^ 2)) s ∧
    -Real.sin (2 * ψ s) * (2 * κ) * (I s * Real.cos (2 * χ s) / n s ^ 2) =
      -2 * κ * (stokesVec (I s) (χ s) (ψ s) 2 / n s ^ 2) := by sorry

end Arxiv1110_5134
