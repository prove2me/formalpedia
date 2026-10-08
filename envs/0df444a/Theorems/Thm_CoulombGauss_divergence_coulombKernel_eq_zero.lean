-- Prove2me | Theorems.Thm_CoulombGauss_divergence_coulombKernel_eq_zero
-- name    : CoulombGauss.divergence_coulombKernel_eq_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T18:18:27.613765+00:00
-- url     : https://prove2.me/theorems/8bfe4c15-4c4b-4cce-9810-d0d8e9817bd9
-- title:
--   $\nabla_r\cdot\frac{r-r'}{|r-r'|^3}=0$ for $r\neq r'$
-- statement:
--   Let $r' \in \mathbb R^3$ be fixed and let $e(r,r') = (r-r')/|r-r'|^3$ be the Coulomb kernel. For every point $r\neq r'$, the map $x\mapsto e(x,r')$ is differentiable at $r$ and
--   $$
--   \nabla_r\cdot e(r,r') \;=\; 0 .
--   $$
--
--   This is the first fact used in the Dirac-delta-free derivation of Gauss's law: away from its source point, the field of a point charge is divergence free.
--
--   **Formalization Note** Differentiability is stated explicitly, because Lean assigns derivative $0$ to non-differentiable functions and the divergence identity alone would otherwise not exclude that degenerate reading.
-- source:
--   Wikipedia, "Coulomb's law", https://en.wikipedia.org/wiki/Coulomb%27s_law (snapshot supplied as PDF, 30 Sep 2026), section "Relation to Gauss's law" -> "Deriving Gauss's law from Coulomb's law", box "Proof (without Dirac Delta)" (PDF pp. 8-9).

import Mathlib
import Definitions.Def_CoulombGauss_basic
open MeasureTheory Filter Topology Metric

namespace CoulombGauss
theorem divergence_coulombKernel_eq_zero (r r' : Vec3) (h : r ≠ r') :
    DifferentiableAt ℝ (fun x => coulombKernel x r') r ∧
      divergence (fun x => coulombKernel x r') r = 0 := by sorry
end CoulombGauss
