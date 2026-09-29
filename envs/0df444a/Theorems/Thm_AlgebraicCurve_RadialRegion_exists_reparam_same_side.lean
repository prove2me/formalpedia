-- Prove2me | Theorems.Thm_AlgebraicCurve_RadialRegion_exists_reparam_same_side
-- name    : AlgebraicCurve.RadialRegion.exists_reparam_same_side
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/acf8a6fc-a964-5441-8f4d-e91e9a5c30bf
-- title:
--   Same-side reparametrisation of a shared straight side of radial regions
-- statement:
--   Four parallel assertions are packaged as a conjunction, one for each of the four coordinate directions. In each, $R$ and $R'$ are radial regions (a centre $q\in\mathbb{C}$, a continuous, $2\pi$-periodic, everywhere positive radius function $r$, and a strictly increasing partition $0=\varphi_0<\dots<\varphi_N=2\pi$ on whose closed subintervals $r$ is $C^2$, with boundary loop $\mathrm{loop}(\varphi)=q+r(\varphi)e^{i\varphi}$), $k$ and $k'$ are indices of arcs of $R$ and $R'$, and $\mathrm{arcIcc}$ denotes the closed parameter interval $[\varphi_{k},\varphi_{k+1}]$ of the corresponding arc. The first assertion assumes $a,a'>0$ with $R.q.\mathrm{re}+a=R'.q.\mathrm{re}+a'$, that $r(t)=(\cos t/a)^{-1}$ on the arc of $R$ and $r(t)=(\cos t/a')^{-1}$ on the arc of $R'$ (so both arcs lie on the common vertical line of that real part), and that each arc interval is contained either in $(-\pi/2,\pi/2)$ or in $(3\pi/2,5\pi/2)$, these two alternatives being chosen independently; the remaining three assertions replace this data by $b,b'>0$ with $R.q.\mathrm{re}-b=R'.q.\mathrm{re}-b'$, $r(t)=(-\cos t/b)^{-1}$ and arcs in $(\pi/2,3\pi/2)$; by $c,c'>0$ with $R.q.\mathrm{im}+c=R'.q.\mathrm{im}+c'$, $r(t)=(\sin t/c)^{-1}$ and arcs in $(0,\pi)$; and by $d,d'>0$ with $R.q.\mathrm{im}-d=R'.q.\mathrm{im}-d'$, $r(t)=(-\sin t/d)^{-1}$ and arcs in $(\pi,2\pi)$. In each case it is further assumed that the two loops agree at the initial parameters of the two arcs and at the terminal parameters. The conclusion is the existence of $\psi:\mathbb{R}\to\mathbb{R}$, strictly increasing and $C^1$ on the parameter interval of the arc of $R'$, carrying the initial and terminal parameters of that arc to those of the arc of $R$, with $R'.\mathrm{loop}(t)=R.\mathrm{loop}(\psi(t))$ for every $t$ in that interval.
--
--   This is the statement that two radial regions presenting pieces of the same straight side (right, left, top or bottom) on a common line, with matching end points in matching order, traverse that side in the same direction, so that one arc is a strictly increasing $C^1$ change of parameter of the other. It is a helper row of the cell-dissection grid construction, used by [`AlgebraicCurve.RadialRegion.exists_grid_geometry`](thm.html#AlgebraicCurve.RadialRegion.exists_grid_geometry) and [`AlgebraicCurve.exists_pairedCellFamily`](thm.html#AlgebraicCurve.exists_pairedCellFamily).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RadialRegion_exists_reparam_same_side.lean

import Definitions.Def_AlgebraicCurve_CellDissection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Real
open AlgebraicCurve Set

theorem AlgebraicCurve.RadialRegion.exists_reparam_same_side :
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (a a' : ℝ), 0 < a → 0 < a' →
      R.q.re + a = R'.q.re + a' →
      (∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / a)⁻¹) →
      (R.arcIcc k ⊆ Ioo (-(π / 2)) (π / 2) ∨ R.arcIcc k ⊆ Ioo (3 * π / 2) (5 * π / 2)) →
      (∀ t ∈ R'.arcIcc k', R'.r t = (Real.cos t / a')⁻¹) →
      (R'.arcIcc k' ⊆ Ioo (-(π / 2)) (π / 2) ∨ R'.arcIcc k' ⊆ Ioo (3 * π / 2) (5 * π / 2)) →
      R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc) →
      R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ) →
      ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
        ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
        ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t)) ∧
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (b b' : ℝ), 0 < b → 0 < b' →
      R.q.re - b = R'.q.re - b' →
      (∀ t ∈ R.arcIcc k, R.r t = (-Real.cos t / b)⁻¹) → R.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2) →
      (∀ t ∈ R'.arcIcc k', R'.r t = (-Real.cos t / b')⁻¹) → R'.arcIcc k' ⊆ Ioo (π / 2) (3 * π / 2) →
      R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc) →
      R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ) →
      ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
        ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
        ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t)) ∧
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (c c' : ℝ), 0 < c → 0 < c' →
      R.q.im + c = R'.q.im + c' →
      (∀ t ∈ R.arcIcc k, R.r t = (Real.sin t / c)⁻¹) → R.arcIcc k ⊆ Ioo 0 π →
      (∀ t ∈ R'.arcIcc k', R'.r t = (Real.sin t / c')⁻¹) → R'.arcIcc k' ⊆ Ioo 0 π →
      R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc) →
      R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ) →
      ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
        ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
        ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t)) ∧
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (d d' : ℝ), 0 < d → 0 < d' →
      R.q.im - d = R'.q.im - d' →
      (∀ t ∈ R.arcIcc k, R.r t = (-Real.sin t / d)⁻¹) → R.arcIcc k ⊆ Ioo π (2 * π) →
      (∀ t ∈ R'.arcIcc k', R'.r t = (-Real.sin t / d')⁻¹) → R'.arcIcc k' ⊆ Ioo π (2 * π) →
      R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.castSucc) →
      R.loop (R.φs k.succ) = R'.loop (R'.φs k'.succ) →
      ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
        ψ (R'.φs k'.castSucc) = R.φs k.castSucc ∧ ψ (R'.φs k'.succ) = R.φs k.succ ∧
        ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t)) := by sorry
