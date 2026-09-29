-- Prove2me | Theorems.Thm_AlgebraicCurve_RadialRegion_exists_recip
-- name    : AlgebraicCurve.RadialRegion.exists_recip
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/e9b7ea56-b045-563e-858a-dfa88f33715f
-- title:
--   Inversion of a radial region centred at the origin
-- statement:
--   Let $R$ be a radial region, i.e. a centre $q \in \mathbb{C}$, a continuous, $2\pi$-periodic, strictly positive radius function $r : \mathbb{R} \to \mathbb{R}$, a number $N$ of arcs and angles $\varphi_0 = 0 < \varphi_1 < \dots < \varphi_N = 2\pi$ such that $r$ is $C^2$ on each $[\varphi_i, \varphi_{i+1}]$; assume $R.q = 0$. Then there is a radial region $R'$ with $R'.q = 0$, with the same number of arcs $R'.N = R.N$, with $0 \in R'.\mathrm{Kint}$, where $\mathrm{Kint}\,S = \{z : \|z - S.q\| < S.r(\arg(z - S.q))\}$, and such that for every $w \neq 0$ one has $w \in R'.K$ exactly when $w^{-1} \notin R.\mathrm{Kint}$, and $w \in R'.\mathrm{Kint}$ exactly when $w^{-1} \notin R.K$ (here `K` is the region attached to a radial region of which `Kint` is the open counterpart); moreover the boundary loops, $S.\mathrm{loop}\,\varphi = S.q + S.r(\varphi)e^{i\varphi}$, satisfy $R'.\mathrm{loop}\,\theta = (R.\mathrm{loop}(2\pi - \theta))^{-1}$ for all real $\theta$. Finally there is a bijection $\sigma : \mathrm{Fin}\,R.N \simeq \mathrm{Fin}\,R'.N$ with $R'.\mathrm{arcIcc}(\sigma k) = (t \mapsto 2\pi - t)[R.\mathrm{arcIcc}\,k]$ and with the image of $R'.\mathrm{arcSet}(\sigma k)$ under $w \mapsto w^{-1}$ equal to $R.\mathrm{arcSet}\,k$, for every arc index $k$.
--
--   This records that inversion about the origin turns the complement of a radial region centred at $0$ into another such region, matching boundary arcs in reversed angular order, in the spirit of the chart at infinity on the Riemann sphere. It is a helper for the cell-dissection existence statement, being used in the proof of [`AlgebraicCurve.exists_pairedCellFamily`](thm.html#AlgebraicCurve.exists_pairedCellFamily).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RadialRegion_exists_recip.lean

import Definitions.Def_AlgebraicCurve_CellDissection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Real
open AlgebraicCurve Set

theorem AlgebraicCurve.RadialRegion.exists_recip (R : RadialRegion) (hq : R.q = 0) :
    ∃ R' : RadialRegion,
      R'.q = 0 ∧ R'.N = R.N ∧ (0 : ℂ) ∈ R'.Kint ∧
      (∀ w : ℂ, w ≠ 0 → (w ∈ R'.K ↔ w⁻¹ ∉ R.Kint)) ∧
      (∀ w : ℂ, w ≠ 0 → (w ∈ R'.Kint ↔ w⁻¹ ∉ R.K)) ∧
      (∀ θ : ℝ, R'.loop θ = (R.loop (2 * π - θ))⁻¹) ∧
      ∃ σ : Fin R.N ≃ Fin R'.N,
        (∀ k : Fin R.N, R'.arcIcc (σ k) = (fun t : ℝ => 2 * π - t) '' R.arcIcc k) ∧
        (∀ k : Fin R.N, (fun w : ℂ => w⁻¹) '' R'.arcSet (σ k) = R.arcSet k) := by sorry
