-- Prove2me | Theorems.Thm_FiniteEnergyPlane_hasWindInfAt_cylInf_of_hasLoopWind
-- name    : FiniteEnergyPlane.hasWindInfAt_cylInf_of_hasLoopWind
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-03T11:33:16.658917+00:00
-- url     : https://prove2.me/theorems/997f934a-2c5b-4bf3-a642-e986bdabe8ac
-- title:
--   The asymptotic winding at $\infty$ is one more than the winding of $\pi\partial_s u$ along large circles
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $J$ a $d\lambda_0$-compatible complex structure on $\xi$, and $\tilde J$ the induced almost complex structure on $\mathbb{R}^4\setminus\{0\}\cong\mathbb{R}\times S$. Let $U\subset\mathbb{C}$ be open with $\{z:|z|>R\}\subset U$, and let $u$ be smooth, nonvanishing and $\tilde J$-holomorphic on $U$. Suppose that the $\xi$-component $\pi\,\partial_s u$, read in Hryniewicz's global frame of $\xi$, has winding number $k$ along every circle $t\mapsto\rho e^{2\pi it}$ with $\rho>R$. Then in the positive cylindrical coordinates $(s,t)\mapsto e^{2\pi(s+it)}$ at $\infty$,
--   $$\mathrm{wind}_\infty(u,\infty)=k+1 .$$
--
--   This expresses the asymptotic winding at the positive puncture $\infty$, which is defined in cylindrical coordinates, through the winding of $\pi\partial_s u$ along large circles in the plane coordinate $z$.
--
--   **Formalization Note** $\mathbb{R}^4$ is `V 1`, $\tilde J$ is `Jtilde H J`, and $\pi\partial_s u$ in the global frame is `piDs H u : ℂ → ℂ`. The circles are `ccwLoop ρ t` $=\rho e^{2\pi it}$. The conclusion is `HasWindInfAt H u cylInf 1 (k + 1)`: for all large $s$ the loop $t\mapsto\pi\partial_s w(s,t)$ of $w=\mathrm{pr}\circ u\circ\mathrm{cylInf}$ has winding number $k+1$. No energy bound or asymptotic hypothesis is assumed.
-- source:
--   U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.2.4 and Lemma 2.15; H. Hofer, K. Wysocki, E. Zehnder, GAFA 5 (1995)

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `u` be smooth, nonvanishing and `J̃`-holomorphic on an open set `U` containing
`{z : R < ‖z‖}`, and suppose that `π ∂ₛu` (in the global frame, `piDs H u`) has winding number `k`
along every counterclockwise circle `t ↦ ρ e^{2πit}` with `ρ > R`. Then the asymptotic winding of
`u` at the positive puncture `∞` in the cylindrical coordinates `cylInf` is `k + 1`. -/
theorem hasWindInfAt_cylInf_of_hasLoopWind (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → V 1) (hu : ContDiffOn ℝ ∞ u U) (hu0 : ∀ z ∈ U, u z ≠ 0)
    (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) U u) (R : ℝ)
    (hRU : ∀ z : ℂ, R < ‖z‖ → z ∈ U) (k : ℤ)
    (hk : ∀ ρ > R, HasLoopWind (fun t => piDs H u (ccwLoop ρ t)) k) :
    HasWindInfAt H u cylInf 1 (k + 1) := by
  sorry

end FiniteEnergyPlane
