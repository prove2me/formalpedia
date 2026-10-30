-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_tendsto_cylEnd_of_isNondegenerate
-- name    : FiniteEnergyPlane.exists_tendsto_cylEnd_of_isNondegenerate
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-29T20:36:49.726022+00:00
-- url     : https://prove2.me/theorems/36c9d4a1-1f7c-40ad-b148-739c69801316
-- title:
--   Ends at nondegenerate orbits converge with a fixed phase
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, $u$ a finite-energy $\tilde J$-holomorphic curve on $D\setminus\{0\}$, $P=(x,T)$ a nondegenerate periodic Reeb orbit and $\sigma=\pm1$. In the cylindrical coordinates $e^{-2\pi(s+it)}$ at $0$ write $a(s,t)$ for the symplectization coordinate of $u$ and $w(s,t)\in S$ for its projection. Assume:
--
--   1. for every $m\ge1$, the $m$-th derivative of $(s,t)\mapsto a(s,t)-\sigma Ts$ tends to $0$ as $s\to+\infty$, uniformly in $t$;
--   2. for every $m\ge0$ and $\varepsilon>0$ there is $s_1$ such that for every $s\ge s_1$ some $c'\in\mathbb{R}$ satisfies $\|D^j\big(w-x(\sigma T\,\cdot_2+c')\big)(s,t)\|\le\varepsilon$ for all $t$ and all $j\le m$.
--
--   Then there are constants $d,c\in\mathbb{R}$ such that, uniformly in $t$ as $s\to+\infty$,
--   $$a(s,t)-\sigma Ts-d\to0,\qquad w(s,t)-x(\sigma Tt+c)\to0.$$
--
--   So at a nondegenerate orbit, convergence of the end to the trivial cylinder up to an $s$-dependent phase and an additive constant improves to convergence with one fixed phase $c$ and one fixed constant $d$.
--
--   **Formalization Note** $a$ and $w$ are `endA H u cylEnd` and `endW H u cylEnd`; derivatives are `iteratedFDeriv ℝ` on $\mathbb{R}\times\mathbb{R}$ with the sup norm on $\mathbb{R}^{2n+2}$; uniform convergence is `TendstoZeroUnif`. In hypothesis 2, $x(\sigma T\,\cdot_2+c')$ is the map $(s,t)\mapsto x(\sigma Tt+c')$.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: Asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996), 337–379, with the Correction, ibid. 15 (1998), 535–538, Lemmas 2.6 and 2.7

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `u` be a finite-energy `J̃`-holomorphic curve on `D \ {0}`, `P = (x, T)` a nondegenerate
periodic Reeb orbit and `σ = ±1`. In the cylindrical coordinates `cylEnd` at `0`, suppose every
derivative of order `≥ 1` of `a(s, t) - σ T s` tends to `0` uniformly in `t`, and that for every
`m` and `ε > 0`, for all large `s` there is a phase `c'` such that the derivatives of order `≤ m`
of `w - x(σ T t + c')` at `(s, t)` are at most `ε` for all `t`. Then there are constants `d, c`
with `a(s, t) - σ T s - d → 0` and `w(s, t) - x(σ T t + c) → 0` uniformly in `t`. -/
theorem exists_tendsto_cylEnd_of_isNondegenerate {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H) (hP : P.IsNondegenerate)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hA : ∀ m : ℕ, 1 ≤ m → ∀ ε > 0, ∃ s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => endA H u cylEnd p - σ * P.T * p.1) (s, t)‖ ≤ ε)
    (hW : ∀ m : ℕ, ∀ ε > 0, ∃ s₁ : ℝ, ∀ s ≥ s₁, ∃ c' : ℝ, ∀ j ≤ m, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ j
        (fun p : ℝ × ℝ => endW H u cylEnd p - P.x (σ * P.T * p.2 + c')) (s, t)‖ ≤ ε) :
    ∃ d c : ℝ,
      TendstoZeroUnif (fun p : ℝ × ℝ => endA H u cylEnd p - σ * P.T * p.1 - d) ∧
        TendstoZeroUnif (fun p : ℝ × ℝ => endW H u cylEnd p - P.x (σ * P.T * p.2 + c)) := by
  sorry

end FiniteEnergyPlane
