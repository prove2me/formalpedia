-- Prove2me | Theorems.Thm_AlgebraicCurve_RadialRegion_exists_pow_pullback_laps
-- name    : AlgebraicCurve.RadialRegion.exists_pow_pullback_laps
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/8765dd45-4e98-5193-acd3-ac57407d8738
-- title:
--   Pullback of a radial region along u↦ q+u^e, with laps
-- statement:
--   Let $R$ be a radial region, i.e. a centre $q\in\mathbb{C}$, a continuous, $2\pi$-periodic, strictly positive radius function $r$ on $\mathbb{R}$, and a subdivision $0=\varphi_0<\varphi_1<\dots<\varphi_N=2\pi$ of $[0,2\pi]$ into $N$ arcs on each of whose closed parameter intervals $r$ is twice continuously differentiable; assume $2\le R.N$ and let $e$ be a nonzero natural number. The assertion is that there is a radial region $R'$ with the following properties: its centre is $0$ and it has $e\cdot R.N$ arcs; a point $u$ lies in the set $R'.K$, respectively in $R'.Kint=\{z:\ \lVert z\rVert<R'.r(\arg z)\}$, exactly when $q+u^{e}$ lies in $R.K$, respectively in $R.Kint$; and for every $\psi\in\mathbb{R}$ one has $q+(R'.\mathrm{loop}\,\psi)^{e}=R.\mathrm{loop}(e\psi)$, where $\mathrm{loop}\,\varphi=q+r(\varphi)e^{i\varphi}$. Moreover there is an indexing $\mathrm{lap}:\mathrm{Fin}\,e\to\mathrm{Fin}\,R.N\to\mathrm{Fin}\,R'.N$ such that $(j,k)\mapsto \mathrm{lap}\,j\,k$ is a bijection, the parameter interval of the arc $\mathrm{lap}\,j\,k$ of $R'$ is the image of that of the $k$-th arc of $R$ under $t\mapsto(2\pi j+t)/e$, the map $u\mapsto q+u^{e}$ sends the arc set of $\mathrm{lap}\,j\,k$ onto the arc set of $k$ and is injective on it, and for each $k$ the $e$ arc sets $\mathrm{lap}\,j\,k$, $j\in\mathrm{Fin}\,e$, can be separated by pairwise disjoint open subsets of $\mathbb{C}$.
--
--   This records, in the language of radial regions, the local normal form $u\mapsto u^{e}$ for an $e$-fold branched covering of a disc-like region: the preimage region is again radial, centred at the origin, and its boundary arcs are grouped into $e$ laps over each boundary arc of the original region, each lap carried bijectively onto its arc and separated from the other laps. It is a step in the grid construction behind the cell-dissection existence statement [`AlgebraicCurve.exists_pairedCellFamily`](thm.html#AlgebraicCurve.exists_pairedCellFamily).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RadialRegion_exists_pow_pullback_laps.lean

import Definitions.Def_AlgebraicCurve_CellDissection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Real
open AlgebraicCurve Set

theorem AlgebraicCurve.RadialRegion.exists_pow_pullback_laps (R : RadialRegion) (hN : 2 ≤ R.N) (e : ℕ) (he : e ≠ 0) :
    ∃ R' : RadialRegion,
      R'.q = 0 ∧ R'.N = e * R.N ∧
      (∀ u : ℂ, u ∈ R'.K ↔ R.q + u ^ e ∈ R.K) ∧
      (∀ u : ℂ, u ∈ R'.Kint ↔ R.q + u ^ e ∈ R.Kint) ∧
      (∀ ψ : ℝ, R.q + R'.loop ψ ^ e = R.loop ((e : ℝ) * ψ)) ∧
      ∃ lap : Fin e → Fin R.N → Fin R'.N,
        Function.Bijective (fun jk : Fin e × Fin R.N => lap jk.1 jk.2) ∧
        (∀ (j : Fin e) (k : Fin R.N),
          R'.arcIcc (lap j k) = (fun t : ℝ => (2 * π * ((j : ℕ) : ℝ) + t) / (e : ℝ)) '' R.arcIcc k) ∧
        (∀ (j : Fin e) (k : Fin R.N),
          (fun u : ℂ => R.q + u ^ e) '' R'.arcSet (lap j k) = R.arcSet k) ∧
        (∀ (j : Fin e) (k : Fin R.N), Set.InjOn (fun u : ℂ => R.q + u ^ e) (R'.arcSet (lap j k))) ∧
        (∀ k : Fin R.N, ∃ U : Fin e → Set ℂ, (∀ j, IsOpen (U j)) ∧
          Pairwise (fun j j' => Disjoint (U j) (U j')) ∧ ∀ j, R'.arcSet (lap j k) ⊆ U j) := by sorry
