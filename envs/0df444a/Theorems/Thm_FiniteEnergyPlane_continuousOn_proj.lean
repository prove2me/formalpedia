-- Prove2me | Theorems.Thm_FiniteEnergyPlane_continuousOn_proj
-- name    : FiniteEnergyPlane.continuousOn_proj
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-25T23:13:05.763477+00:00
-- url     : https://prove2.me/theorems/b37b5ef6-2239-41a1-b750-484fd64dc68f
-- title:
--   Radial projection onto a star-shaped level is continuous
-- statement:
--   Let $H:\mathbb R^{2n+2}\to\mathbb R$ be smooth with a strictly star-shaped level $S=H^{-1}(1)$: every ray from the origin meets $S$ exactly once, and transversally ($dH(x)\,x>0$ for $x\in S$). For $y\neq 0$ let $r(y)>0$ be the unique scalar with $H(r(y)\,y)=1$. Then the radial projection
--   $$\mathrm{proj}_H:\mathbb R^{2n+2}\setminus\{0\}\to S,\qquad y\mapsto r(y)\,y,$$
--   is continuous.
--
--   This is the continuity part of the standard identification of the symplectization $\mathbb R\times S$ with $\mathbb R^{2n+2}\setminus\{0\}$. It follows, for instance, from the implicit function theorem applied to $(r,y)\mapsto H(ry)-1$ at $(r(y),y)$, since $\partial_r H(ry)=dH(ry)\,y=r^{-1}\,dH(ry)(ry)>0$ there.
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), § 1; U. Hryniewicz, J. Symplectic Geom. 12 (2014), § 2.2 (identification of R × S with R^{2n+2} \ {0})

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- On a strictly star-shaped level `S = H⁻¹(1)`, the radial projection
`proj H : V n \ {0} → S`, `y ↦ r(y) y` with `r(y) > 0` the unique scalar with `H(r(y) y) = 1`,
is continuous on `V n \ {0}`. -/
theorem continuousOn_proj {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) :
    ContinuousOn (proj H) {0}ᶜ := by
  sorry

end FiniteEnergyPlane
