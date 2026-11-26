-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_spanningDisk_of_isUnknotted
-- name    : FiniteEnergyPlane.exists_spanningDisk_of_isUnknotted
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T23:03:46.479533+00:00
-- url     : https://prove2.me/theorems/ed710a30-4148-50fa-ac2e-23882f518aa7
-- title:
--   Spanning disks of unknotted periodic orbits
-- statement:
--   Let $S=H_0^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $P=(x,T)$ an unknotted periodic orbit of $X_{H_0}$ on $S$. Then there are $\rho>1$ and a smooth $e:\mathbb{C}\to\mathbb{R}^4$ that embeds the open disk of radius $\rho$ into $S$, maps the unit circle onto $x(\mathbb{R})$, and satisfies
--   $$\lambda_0\big(De(z)\,iz\big)>0\qquad\text{for }|z|=1 .$$
--
--   Unknotted means that $x(\mathbb{R})$ bounds a smoothly embedded closed disk in $S$. The spanning disk obtained is parametrized beyond its boundary, which is oriented by the flow.
--
--   **Formalization Note** Periodic orbits $P$ of $X_{H_0}$ are those of `HryniewiczCriterion_Basic`, in the coordinates `R4`; the level and the orbit are transported by the coordinate-preserving identification `ofR4` with `V 1`. The conclusion is `IsSpanningDisk`.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), 791–862, arXiv:1105.2077, § 3.1

import Definitions.Def_FiniteEnergyPlane_DiskFoliation
import Definitions.Def_HryniewiczCriterion_GlobalSection

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hryniewicz (2014), § 3.1. An unknotted periodic orbit of a strictly star-shaped level, transported to `V 1`
by `ofR4`, has a spanning disk parametrized slightly beyond its boundary, with the boundary oriented by `λ₀`. -/
theorem exists_spanningDisk_of_isUnknotted (H₀ : HryniewiczCriterion.R4 → ℝ)
    (hH₀ : HryniewiczCriterion.IsStrictlyStarShapedLevel H₀) (P : HryniewiczCriterion.PeriodicOrbit H₀)
    (hu : HryniewiczCriterion.IsUnknotted H₀ P) :
    let H : V 1 → ℝ := fun y => H₀ (fun k => y (Fin.cast (by norm_num) k))
    ∃ (e : ℂ → V 1) (ρ : ℝ), IsSpanningDisk H (Set.range fun τ => ofR4 (P.x τ)) e ρ := by
  sorry

end FiniteEnergyPlane
