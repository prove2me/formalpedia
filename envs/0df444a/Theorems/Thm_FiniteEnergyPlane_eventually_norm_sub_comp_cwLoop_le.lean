-- Prove2me | Theorems.Thm_FiniteEnergyPlane_eventually_norm_sub_comp_cwLoop_le
-- name    : FiniteEnergyPlane.eventually_norm_sub_comp_cwLoop_le
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-25T23:13:06.163418+00:00
-- url     : https://prove2.me/theorems/f737dd05-bf51-4f2b-97d9-01c9c3a9845b
-- title:
--   Circle loops of a continuous map depend uniformly continuously on the radius
-- statement:
--   Let $E$ be a normed group, $z_0\in\mathbb C$, $R>0$, and let $F:\mathbb C\to E$ be continuous on the punctured disc $B(z_0,R)\setminus\{z_0\}$. For $0<r_0<R$ and every $\varepsilon>0$ there is a neighbourhood of $r_0$ such that for all $r$ in it
--   $$\sup_{t\in\mathbb R}\big\|F(z_0+r e^{-2\pi i t})-F(z_0+r_0 e^{-2\pi i t})\big\|\le\varepsilon .$$
--   In other words, the clockwise loops $t\mapsto F(z_0+re^{-2\pi i t})$ depend continuously on the radius $r\in(0,R)$ in the uniform ($C^0$) topology. This follows from uniform continuity of $F$ on a compact annulus $\{r_0-\eta\le |z-z_0|\le r_0+\eta\}$ contained in the punctured disc.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, proof of Lemma 9.18, p. 170 (continuity of the loops in the radius, used for the connectedness argument)

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- If `F` is continuous on the punctured disc `B(z₀, R) \ {z₀}` and `0 < r₀ < R`, then the loops
`t ↦ F(z₀ + r e^{-2π i t})` converge uniformly in `t ∈ ℝ` to the loop of radius `r₀` as `r → r₀`. -/
theorem eventually_norm_sub_comp_cwLoop_le {E : Type*} [NormedAddCommGroup E] (F : ℂ → E)
    (z₀ : ℂ) (R : ℝ) (hF : ContinuousOn F (ball z₀ R \ {z₀})) (r₀ : ℝ) (hr₀ : r₀ ∈ Set.Ioo 0 R)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r in 𝓝 r₀, ∀ t : ℝ, ‖F (cwLoop z₀ r t) - F (cwLoop z₀ r₀ t)‖ ≤ ε := by
  sorry

end FiniteEnergyPlane
