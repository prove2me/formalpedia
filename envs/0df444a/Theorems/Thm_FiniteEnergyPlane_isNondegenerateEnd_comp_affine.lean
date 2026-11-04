-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isNondegenerateEnd_comp_affine
-- name    : FiniteEnergyPlane.isNondegenerateEnd_comp_affine
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-03T09:21:59.00119+00:00
-- url     : https://prove2.me/theorems/21981632-065d-444b-9cdf-9cfa80d7f92d
-- title:
--   A nondegenerate end at a puncture $z_0$, read at the puncture $0$ of the unit disc
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$, let $P=(x,T)$ be a periodic Reeb orbit on $S$ and $\varepsilon\in\{\pm1\}$. Let $u:\mathbb{C}\to\mathbb{R}^{2n+2}$, $z_0\in\mathbb{C}$ and $r>0$. Suppose that in the cylindrical coordinates $(s,t)\mapsto z_0+e^{-2\pi(s+it)}$ at $z_0$, $u$ has a nondegenerate end over $P$ with sign $\varepsilon$ (Hryniewicz, Definition 2.9 (1), (2), (4)): for some $d,c\in\mathbb{R}$ and $b>0$, $a(s,t)-\varepsilon Ts-d\to0$ and $e^{bs}\big(w(s,t)-x(\varepsilon Tt+c)\big)\to0$ uniformly in $t$ as $s\to+\infty$, where $a$ and $w$ are the $\mathbb{R}$- and $S$-components of $u$. Then $\tilde u(z)=u(z_0+rz)$ has a nondegenerate end over the same $P$ with the same sign $\varepsilon$ in the cylindrical coordinates $(s,t)\mapsto e^{-2\pi(s+it)}$ at $0$.
--
--   Together with the corresponding statement for the curve itself, this moves results about nondegenerate punctures at $0$ of the unit disc to any puncture $z_0$.
--
--   **Formalization Note** $\mathbb{R}^{2n+2}$ is `V n`; the nondegenerate end is `IsNondegenerateEnd H u e P ε` with `e = cylEndAt z₀` (hypothesis) and `e = cylEnd` (conclusion). The constants $d,c,b$ of the conclusion need not equal those of the hypothesis.
-- source:
--   U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Definition 2.9 (nondegenerate punctures); standard change of coordinates

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- If `u` has a nondegenerate end at the puncture `z₀` (cylindrical coordinates `cylEndAt z₀`)
over `P` with sign `ε`, then `z ↦ u (z₀ + r z)` (`r > 0`) has a nondegenerate end at `0` (cylindrical
coordinates `cylEnd`) over the same `P` with the same sign. -/
theorem isNondegenerateEnd_comp_affine {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) (z₀ : ℂ) (r : ℝ)
    (hr : 0 < r) (P : ReebOrbit H) (ε : ℝ) (hnd : IsNondegenerateEnd H u (cylEndAt z₀) P ε) :
    IsNondegenerateEnd H (fun z => u (z₀ + (r : ℂ) * z)) cylEnd P ε := by
  sorry

end FiniteEnergyPlane
