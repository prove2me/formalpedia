-- Prove2me | Theorems.Thm_AlgebraicCurve_RadialRegion_exists_reparam_across_edge
-- name    : AlgebraicCurve.RadialRegion.exists_reparam_across_edge
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/0efe5e11-45b5-5566-b1ed-141a5019fb40
-- title:
--   Reparametrising a shared straight edge of two radial regions
-- statement:
--   A `RadialRegion` consists of a centre $q \in \mathbb{C}$, a continuous, $2\pi$-periodic, strictly positive radius function $r$ on $\mathbb{R}$, a natural number $N$ and a strictly increasing sequence $\varphi_0 = 0 < \dots < \varphi_N = 2\pi$ such that $r$ is twice continuously differentiable on each $[\varphi_{k}, \varphi_{k+1}]$; its boundary loop is $\mathrm{loop}(\varphi) = q + r(\varphi)e^{i\varphi}$ and $\mathrm{arcIcc}\,k = [\varphi_{k}, \varphi_{k+1}]$. The theorem is the conjunction of two parallel assertions, one for a vertical and one for a horizontal shared edge. Vertical case: for all radial regions $R, R'$, indices $k < R.N$, $k' < R'.N$ and reals $a, b > 0$ with $\operatorname{Re} R.q + a = \operatorname{Re} R'.q - b$, assume $R.r(t) = (\cos t / a)^{-1}$ for all $t$ in $R.\mathrm{arcIcc}\,k$, that this interval lies in $(-\pi/2, \pi/2)$ or in $(3\pi/2, 5\pi/2)$, that $R'.r(t) = (-\cos t / b)^{-1}$ for all $t$ in $R'.\mathrm{arcIcc}\,k'$, that this interval lies in $(\pi/2, 3\pi/2)$, and that the endpoints match crosswise: $R.\mathrm{loop}(\varphi_{k}) = R'.\mathrm{loop}(\varphi'_{k'+1})$ and $R.\mathrm{loop}(\varphi_{k+1}) = R'.\mathrm{loop}(\varphi'_{k'})$. Then there is $\psi : \mathbb{R} \to \mathbb{R}$, strictly decreasing and $C^1$ on $R'.\mathrm{arcIcc}\,k'$, with $\psi(\varphi'_{k'}) = \varphi_{k+1}$, $\psi(\varphi'_{k'+1}) = \varphi_{k}$ and $R'.\mathrm{loop}(t) = R.\mathrm{loop}(\psi(t))$ for every $t$ in $R'.\mathrm{arcIcc}\,k'$. Horizontal case: the same with $c, d > 0$, $\operatorname{Im} R.q + c = \operatorname{Im} R'.q - d$, $R.r(t) = (\sin t / c)^{-1}$ on $R.\mathrm{arcIcc}\,k \subseteq (0, \pi)$ and $R'.r(t) = (-\sin t / d)^{-1}$ on $R'.\mathrm{arcIcc}\,k' \subseteq (\pi, 2\pi)$, and the same conclusion.
--
--   The radius conditions say precisely that the arc of $R$ traces a segment of the vertical (resp. horizontal) line at signed distance $a$ (resp. $c$) from the centre of $R$, and the arc of $R'$ a segment of the same line at distance $b$ (resp. $d$) on the other side; the conclusion expresses that the two arcs are the same segment traversed in opposite senses, via an orientation-reversing $C^1$ change of parameter. It is a geometric ingredient of the cell-dissection construction, used by [`AlgebraicCurve.RadialRegion.exists_grid_geometry`](thm.html#AlgebraicCurve.RadialRegion.exists_grid_geometry) and [`AlgebraicCurve.exists_pairedCellFamily`](thm.html#AlgebraicCurve.exists_pairedCellFamily).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RadialRegion_exists_reparam_across_edge.lean

import Definitions.Def_AlgebraicCurve_CellDissection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Real
open AlgebraicCurve Set

theorem AlgebraicCurve.RadialRegion.exists_reparam_across_edge :
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (a b : ℝ), 0 < a → 0 < b →
      R.q.re + a = R'.q.re - b →
      (∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / a)⁻¹) →
      (R.arcIcc k ⊆ Ioo (-(π / 2)) (π / 2) ∨ R.arcIcc k ⊆ Ioo (3 * π / 2) (5 * π / 2)) →
      (∀ t ∈ R'.arcIcc k', R'.r t = (-Real.cos t / b)⁻¹) →
      R'.arcIcc k' ⊆ Ioo (π / 2) (3 * π / 2) →
      R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.succ) →
      R.loop (R.φs k.succ) = R'.loop (R'.φs k'.castSucc) →
      ∃ ψ : ℝ → ℝ, StrictAntiOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
        ψ (R'.φs k'.castSucc) = R.φs k.succ ∧ ψ (R'.φs k'.succ) = R.φs k.castSucc ∧
        ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t)) ∧
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (c d : ℝ), 0 < c → 0 < d →
      R.q.im + c = R'.q.im - d →
      (∀ t ∈ R.arcIcc k, R.r t = (Real.sin t / c)⁻¹) → R.arcIcc k ⊆ Ioo 0 π →
      (∀ t ∈ R'.arcIcc k', R'.r t = (-Real.sin t / d)⁻¹) → R'.arcIcc k' ⊆ Ioo π (2 * π) →
      R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.succ) →
      R.loop (R.φs k.succ) = R'.loop (R'.φs k'.castSucc) →
      ∃ ψ : ℝ → ℝ, StrictAntiOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
        ψ (R'.φs k'.castSucc) = R.φs k.succ ∧ ψ (R'.φs k'.succ) = R.φs k.castSucc ∧
        ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t)) := by sorry
