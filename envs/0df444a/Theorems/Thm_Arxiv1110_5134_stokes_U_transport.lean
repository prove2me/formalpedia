-- Prove2me | Theorems.Thm_Arxiv1110_5134_stokes_U_transport
-- name    : Arxiv1110_5134.stokes_U_transport
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:02:47.338084+00:00
-- url     : https://prove2.me/theorems/de018d84-3616-458b-aae6-fba58a377efc
-- title:
--   Eq. (12): transport law for $U/n^2$
-- statement:
--   Under the hypotheses of Eq. (11): $\frac{d}{ds}[I/n^2]=0$, $d\chi/ds=0$ and $d\psi/ds=\kappa$ at a point of a ray with $n>0$. Then the third Stokes component $U=I\cos2\chi\sin2\psi$ satisfies (Eq. 12)
--
--   $$\frac{d}{ds}\Big[\frac{U}{n^2}\Big]=\frac{I\cos2\chi}{n^2}\frac{d}{ds}[\sin2\psi]=\frac{I\cos2\chi\cos2\psi}{n^2}\frac{d(2\psi)}{ds}=2\kappa\frac{Q}{n^2}.$$
--
--   **Formalization Note** The statement is at a single point $s$ of the ray.
-- source:
--   Zhao, Tan and Liu, On the Derivation of Vector Radiative Transfer Equation for Polarized Radiative Transport in Graded Index Media, arXiv:1110.5134v1 (2011), claim c004; Section 3.1, Eq. (12), PDF p. 10

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic

open MeasureTheory Filter Topology
open scoped Matrix

namespace Arxiv1110_5134

theorem stokes_U_transport (n I χ ψ : ℝ → ℝ) (κ s : ℝ) (hn : 0 < n s)
    (hI : HasDerivAt (fun t => I t / n t ^ 2) 0 s) (hχ : HasDerivAt χ 0 s)
    (hψ : HasDerivAt ψ κ s) :
    HasDerivAt (fun t => stokesVec (I t) (χ t) (ψ t) 2 / n t ^ 2)
      (I s * Real.cos (2 * χ s) / n s ^ 2 * (2 * Real.cos (2 * ψ s) * κ)) s ∧
    I s * Real.cos (2 * χ s) / n s ^ 2 * (2 * Real.cos (2 * ψ s) * κ) =
      I s * Real.cos (2 * χ s) * Real.cos (2 * ψ s) / n s ^ 2 * (2 * κ) ∧
    I s * Real.cos (2 * χ s) * Real.cos (2 * ψ s) / n s ^ 2 * (2 * κ) =
      2 * κ * (stokesVec (I s) (χ s) (ψ s) 1 / n s ^ 2) := by sorry

end Arxiv1110_5134
