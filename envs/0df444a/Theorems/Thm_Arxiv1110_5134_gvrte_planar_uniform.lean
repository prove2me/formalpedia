-- Prove2me | Theorems.Thm_Arxiv1110_5134_gvrte_planar_uniform
-- name    : Arxiv1110_5134.gvrte_planar_uniform
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T09:05:27.712208+00:00
-- url     : https://prove2.me/theorems/c697334a-c1d2-4547-8462-1d22fcd66a52
-- title:
--   Eqs. (15)-(16): planar rays and uniform refractive index
-- statement:
--   Under the hypotheses of Eq. (13), suppose the ray is a plane curve, so $\kappa=0$ and Rytov's law gives $d\psi/ds=0$. Then (Eq. 15)
--
--   $$\frac{d}{ds}\Big[\frac{\mathbf I}{n^2}\Big]=0.$$
--
--   If in addition the refractive index is uniform, then (Eq. 16)
--
--   $$\frac{d\mathbf I}{ds}=0,$$
--
--   which is the conservation of Stokes parameters in the classic VRTE for non-participating media.
--
--   **Formalization Note** The statement is at a single point $s$. A uniform refractive index means that $n$ is a constant function.
-- source:
--   Zhao, Tan and Liu, On the Derivation of Vector Radiative Transfer Equation for Polarized Radiative Transport in Graded Index Media, arXiv:1110.5134v1 (2011), claim c006; Section 3.1, Eqs. (15)-(16), PDF pp. 10-11

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic

open MeasureTheory Filter Topology
open scoped Matrix

namespace Arxiv1110_5134

theorem gvrte_planar_uniform (n I χ ψ : ℝ → ℝ) (s : ℝ) (hn : 0 < n s)
    (hI : HasDerivAt (fun t => I t / n t ^ 2) 0 s) (hχ : HasDerivAt χ 0 s)
    (hψ : HasDerivAt ψ 0 s) :
    HasDerivAt (fun t => (n t ^ 2)⁻¹ • stokesVec (I t) (χ t) (ψ t)) 0 s ∧
    ((∃ n₀ : ℝ, ∀ t, n t = n₀) →
      HasDerivAt (fun t => stokesVec (I t) (χ t) (ψ t)) 0 s) := by sorry

end Arxiv1110_5134
