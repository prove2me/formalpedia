-- Prove2me | Theorems.Thm_FiniteEnergyPlane_hasWindInfAt_cylEndAt_of_hasLoopWind
-- name    : FiniteEnergyPlane.hasWindInfAt_cylEndAt_of_hasLoopWind
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-03T11:33:17.793031+00:00
-- url     : https://prove2.me/theorems/59e066d5-7165-4c6c-afdd-aa23e44dea40
-- title:
--   The asymptotic winding at a negative puncture is one more than the winding of $\pi\partial_s u$ along small circles
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $J$ a $d\lambda_0$-compatible complex structure on $\xi$, and $\tilde J$ the induced almost complex structure on $\mathbb{R}^4\setminus\{0\}\cong\mathbb{R}\times S$. Let $U\subset\mathbb{C}$ be open and contain the punctured disc $B(z_0,r)\setminus\{z_0\}$, $r>0$, and let $u$ be smooth, nonvanishing and $\tilde J$-holomorphic on $U$. Suppose that the $\xi$-component $\pi\,\partial_s u$, read in Hryniewicz's global frame of $\xi$, has winding number $k$ along every counterclockwise circle $t\mapsto z_0+\rho e^{2\pi it}$ with $0<\rho<r$. Then at $z_0$ seen as a negative puncture, in the cylindrical coordinates $(s,t)\mapsto z_0+e^{-2\pi(s+it)}$ with $t$ traversed backwards (sign $-1$),
--   $$\mathrm{wind}_\infty(u,z_0)=k+1 .$$
--
--   This expresses the asymptotic winding at a negative puncture, which is defined in cylindrical coordinates, through the winding of $\pi\partial_s u$ along small counterclockwise circles about $z_0$ in the plane coordinate.
--
--   **Formalization Note** $\mathbb{R}^4$ is `V 1`, $\tilde J$ is `Jtilde H J`, and $\pi\partial_s u$ in the global frame is `piDs H u : ℂ → ℂ`. The circles are `z₀ + ccwLoop ρ t`. The conclusion is `HasWindInfAt H u (cylEndAt z₀) (-1) (k + 1)`: for all large $s$ the loop $t\mapsto\pi\partial_s w(s,-t)$ of $w=\mathrm{pr}\circ u\circ\mathrm{cylEndAt}\,z_0$ has winding number $k+1$. No energy bound or asymptotic hypothesis is assumed.
-- source:
--   U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.2.4 and Lemma 2.15; H. Hofer, K. Wysocki, E. Zehnder, GAFA 5 (1995)

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `u` be smooth, nonvanishing and `J̃`-holomorphic on an open set `U` containing the punctured
disc `B(z₀, r) \ {z₀}`, and suppose that `π ∂ₛu` (in the global frame, `piDs H u`) has winding
number `k` along every counterclockwise circle `t ↦ z₀ + ρ e^{2πit}` with `0 < ρ < r`. Then the
asymptotic winding of `u` at `z₀`, viewed as a negative puncture in the cylindrical coordinates
`cylEndAt z₀` (sign `-1`), is `k + 1`. -/
theorem hasWindInfAt_cylEndAt_of_hasLoopWind (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → V 1) (hu : ContDiffOn ℝ ∞ u U) (hu0 : ∀ z ∈ U, u z ≠ 0)
    (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) U u) (z₀ : ℂ) (r : ℝ) (hr : 0 < r)
    (hrU : ball z₀ r \ {z₀} ⊆ U) (k : ℤ)
    (hk : ∀ ρ ∈ Set.Ioo 0 r, HasLoopWind (fun t => piDs H u (z₀ + ccwLoop ρ t)) k) :
    HasWindInfAt H u (cylEndAt z₀) (-1) (k + 1) := by
  sorry

end FiniteEnergyPlane
