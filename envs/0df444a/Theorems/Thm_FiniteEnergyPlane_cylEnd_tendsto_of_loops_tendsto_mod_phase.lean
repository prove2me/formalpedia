-- Prove2me | Theorems.Thm_FiniteEnergyPlane_cylEnd_tendsto_of_loops_tendsto_mod_phase
-- name    : FiniteEnergyPlane.cylEnd_tendsto_of_loops_tendsto_mod_phase
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-29T20:36:09.863789+00:00
-- url     : https://prove2.me/theorems/86ef180a-0fb4-43fb-941b-c8af30f754d8
-- title:
--   Loop convergence up to phase gives $C^\infty$ convergence of the end up to phase
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, $u$ a finite-energy $\tilde J$-holomorphic curve on $D\setminus\{0\}$, $P=(x,T)$ a periodic Reeb orbit (not assumed nondegenerate) and $\sigma=\pm1$. Suppose that for every $m\ge0$ and $\varepsilon>0$ there is $r_0>0$ such that for every $0<r<r_0$ some $c'\in\mathbb{R}$ satisfies
--   $$\sup_{t\in\mathbb{R}}\Big\|\tfrac{d^j}{dt^j}\Big(\mathrm{proj}\,u(re^{-2\pi it})-x(\sigma Tt+c')\Big)\Big\|\le\varepsilon\qquad(0\le j\le m).$$
--   In the cylindrical coordinates $e^{-2\pi(s+it)}$ at $0$ write $a(s,t)$ for the symplectization coordinate of $u$ and $w(s,t)\in S$ for its projection. Then:
--
--   1. $a$ and $w$ are $C^\infty$ on $(s_0,\infty)\times\mathbb{R}$ for some $s_0$;
--   2. for every $m\ge1$, the $m$-th derivative of $(s,t)\mapsto a(s,t)-\sigma Ts$ tends to $0$ as $s\to+\infty$, uniformly in $t$;
--   3. for every $m\ge0$ and $\varepsilon>0$ there is $s_1$ such that for every $s\ge s_1$ some $c'\in\mathbb{R}$ satisfies $\|D^j\big(w-x(\sigma T\,\cdot_2+c')\big)(s,t)\|\le\varepsilon$ for all $t$ and all $j\le m$, where $x(\sigma T\,\cdot_2+c')$ denotes $(s,t)\mapsto x(\sigma Tt+c')$.
--
--   This says that $C^\infty$ convergence of the boundary loops up to reparametrization implies $C^\infty$ convergence of the whole end, in both variables, to the trivial cylinder over $P$ up to a phase that may depend on $s$ and up to an additive constant in $a$.
--
--   **Formalization Note** $a$ and $w$ are `endA H u cylEnd` and `endW H u cylEnd`; derivatives are `iteratedFDeriv ℝ` on $\mathbb{R}\times\mathbb{R}$ (and `iteratedDeriv` for the loops), with the sup norm on $\mathbb{R}^{2n+2}$. The hypothesis has exactly the form of the conclusion of `FiniteEnergyPlane.tendstoCInfty_of_isIsolated`.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: Asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996), 337–379, with the Correction, ibid. 15 (1998), 535–538, Lemma 2.4

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `u` be a finite-energy `J̃`-holomorphic curve on `D \ {0}`, `P = (x, T)` a periodic Reeb
orbit and `σ = ±1`. Suppose that for every `m` and `ε > 0`, every clockwise loop
`t ↦ proj(u(r e^{-2π i t}))` of sufficiently small radius `r > 0` is `ε`-close in `C^m` to some
reparametrization `t ↦ x(σ T t + c')`. Then, in the cylindrical coordinates `cylEnd` at `0`, the
maps `a(s, t)` and `w(s, t)` are smooth for large `s`, every derivative of order `≥ 1` of
`a(s, t) - σ T s` tends to `0` uniformly in `t`, and for every `m` and `ε > 0`, for all large `s`
there is a phase `c'` such that the derivatives of order `≤ m` of `w - x(σ T t + c')` at `(s, t)`
are at most `ε` for all `t`. -/
theorem cylEnd_tendsto_of_loops_tendsto_mod_phase {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1)
    (hloop : ∀ m : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ r in 𝓝[>] (0 : ℝ), ∃ c' : ℝ, ∀ j ≤ m, ∀ t : ℝ,
      ‖iteratedDeriv j (loopInS H u (cwLoop 0 r)) t -
        iteratedDeriv j (fun t => P.x (σ * P.T * t + c')) t‖ ≤ ε) :
    (∃ s₀ : ℝ, ContDiffOn ℝ ∞ (endA H u cylEnd) (Set.Ioi s₀ ×ˢ Set.univ) ∧
        ContDiffOn ℝ ∞ (endW H u cylEnd) (Set.Ioi s₀ ×ˢ Set.univ)) ∧
      (∀ m : ℕ, 1 ≤ m → ∀ ε > 0, ∃ s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
        ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => endA H u cylEnd p - σ * P.T * p.1) (s, t)‖ ≤ ε) ∧
      ∀ m : ℕ, ∀ ε > 0, ∃ s₁ : ℝ, ∀ s ≥ s₁, ∃ c' : ℝ, ∀ j ≤ m, ∀ t : ℝ,
        ‖iteratedFDeriv ℝ j
          (fun p : ℝ × ℝ => endW H u cylEnd p - P.x (σ * P.T * p.2 + c')) (s, t)‖ ≤ ε := by
  sorry

end FiniteEnergyPlane
