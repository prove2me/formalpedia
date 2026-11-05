-- Prove2me | Theorems.Thm_FiniteEnergyPlane_hasLoopWind_cylInf_of_hasLoopWind_circle
-- name    : FiniteEnergyPlane.hasLoopWind_cylInf_of_hasLoopWind_circle
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T20:11:18.532065+00:00
-- url     : https://prove2.me/theorems/4b079f4a-249e-4123-b8d4-f509b50aa6e7
-- title:
--   Winding of $\pi\partial_s u$ along one circle versus in cylindrical coordinates at $\infty$
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $J$ a $d\lambda_0$-compatible complex structure on $\xi$, and $\tilde J$ the induced almost complex structure on $\mathbb{R}^4\setminus\{0\}\cong\mathbb{R}\times S$. Let $U\subset\mathbb{C}$ be open, $u$ smooth, nonvanishing and $\tilde J$-holomorphic on $U$, and $s\in\mathbb{R}$ such that the circle $|z|=e^{2\pi s}$ lies in $U$. Suppose that the $\xi$-component $\pi\,\partial_s u$, read in Hryniewicz's global frame of $\xi$, has winding number $k$ along $t\mapsto e^{2\pi s}e^{2\pi it}$. Then the loop $t\mapsto\pi\partial_s w(s,t)$ of $w=\mathrm{pr}\circ u\circ\mathrm{cylInf}$, in the cylindrical coordinates $(s,t)\mapsto e^{2\pi(s+it)}$ at $\infty$, has winding number $k+1$ in the same frame.
--
--   This compares the two natural loops attached to a single circle: the section read in the plane coordinate $z$ and the same section read in cylindrical coordinates. It holds at each individual radius, with no condition on the other circles.
--
--   **Formalization Note** $\mathbb{R}^4$ is `V 1`, $\tilde J$ is `Jtilde H J`, and $\pi\partial_s u$ in the global frame is `piDs H u : ℂ → ℂ`. The circle is `ccwLoop (Real.exp (2 * π * s)) t`. The hypothesis `HasLoopWind` includes that `piDs H u` has no zero on the circle. No energy bound or asymptotic hypothesis is assumed.
-- source:
--   U. Hryniewicz, Trans. AMS 364 (2012), arXiv:1105.2077, Section 4.6; H. Hofer, K. Wysocki, E. Zehnder, GAFA 5 (1995)

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `u` be smooth, nonvanishing and `J̃`-holomorphic on an open set `U` containing the circle
of radius `e^{2π s}`. If `π ∂ₛu` (in the global frame, `piDs H u`) has winding number `k` along
that circle, then the loop `t ↦ π ∂ₛw(s, t)` in the cylindrical coordinates `cylInf` has winding
number `k + 1`. -/
theorem hasLoopWind_cylInf_of_hasLoopWind_circle (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → V 1) (hu : ContDiffOn ℝ ∞ u U) (hu0 : ∀ z ∈ U, u z ≠ 0)
    (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) U u) (s : ℝ)
    (hmem : ∀ t, ccwLoop (Real.exp (2 * π * s)) t ∈ U) (k : ℤ)
    (hk : HasLoopWind (fun t => piDs H u (ccwLoop (Real.exp (2 * π * s)) t)) k) :
    HasLoopWind (fun t => xiCoordC H (endW H u cylInf (s, t))
      (piXi H (endW H u cylInf (s, t)) (fderiv ℝ (endW H u cylInf) (s, t) (1, 0)))) (k + 1) := by
  sorry

end FiniteEnergyPlane
