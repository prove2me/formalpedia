-- Prove2me | Theorems.Thm_Arxiv1110_5134_stokes_V_invariant
-- name    : Arxiv1110_5134.stokes_V_invariant
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T09:00:01.14853+00:00
-- url     : https://prove2.me/theorems/1fe61bd3-6c2a-4387-8046-735edbc05bdd
-- title:
--   Eq. (8): $V/n^2$ is invariant along a ray
-- statement:
--   Along a ray in a non-participating graded index medium with arc length $s$ and refractive index $n(s)>0$, suppose the Clausius invariant $\frac{d}{ds}[I/n^2]=0$ holds (Eq. 3) and the ellipticity angle $\chi$ is conserved, $d\chi/ds=0$. Then the fourth Stokes component $V=I\sin2\chi$ satisfies (Eq. 8)
--
--   $$\frac{d}{ds}\Big[\frac{V}{n^2}\Big]=\frac{d}{ds}\Big[\frac{I\sin2\chi}{n^2}\Big]=0.$$
--
--   **Formalization Note** The statement is at a single point $s$ of the ray, and the hypotheses are required only at that point. Applied at every point, it gives the paper's statement along the ray.
-- source:
--   Zhao, Tan and Liu, On the Derivation of Vector Radiative Transfer Equation for Polarized Radiative Transport in Graded Index Media, arXiv:1110.5134v1 (2011), claim c002; Section 2.3, Eq. (8), PDF p. 8

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic

open MeasureTheory Filter Topology
open scoped Matrix

namespace Arxiv1110_5134

theorem stokes_V_invariant (n I χ ψ : ℝ → ℝ) (s : ℝ) (hn : 0 < n s)
    (hI : HasDerivAt (fun t => I t / n t ^ 2) 0 s) (hχ : HasDerivAt χ 0 s) :
    HasDerivAt (fun t => stokesVec (I t) (χ t) (ψ t) 3 / n t ^ 2) 0 s := by sorry

end Arxiv1110_5134
