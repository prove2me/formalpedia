-- Prove2me | Theorems.Thm_FiniteEnergyPlane_tendstoZeroCInfty_of_tendstoZeroUnif_mod_phase
-- name    : FiniteEnergyPlane.tendstoZeroCInfty_of_tendstoZeroUnif_mod_phase
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-29T20:37:29.9365+00:00
-- url     : https://prove2.me/theorems/98090056-503a-4904-8567-156ad9030abb
-- title:
--   Fixed-phase $C^0$ convergence and $C^\infty$ convergence up to phase give $C^\infty$ convergence
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level, $P=(x,T)$ a periodic Reeb orbit on $S$ and $\sigma=\pm1$. Let $A:\mathbb{R}^2\to\mathbb{R}$ and $W:\mathbb{R}^2\to\mathbb{R}^{2n+2}$ be $C^\infty$ on $(s_0,\infty)\times\mathbb{R}$ for some $s_0$, and $d,c\in\mathbb{R}$. Assume:
--
--   1. for every $m\ge1$, the $m$-th derivative of $(s,t)\mapsto A(s,t)-\sigma Ts$ tends to $0$ as $s\to+\infty$, uniformly in $t$;
--   2. for every $m\ge0$ and $\varepsilon>0$ there is $s_1$ such that for every $s\ge s_1$ some $c'\in\mathbb{R}$ satisfies $\|D^j\big(W-x(\sigma T\,\cdot_2+c')\big)(s,t)\|\le\varepsilon$ for all $t$ and all $j\le m$;
--   3. $A(s,t)-\sigma Ts-d\to0$ and $W(s,t)-x(\sigma Tt+c)\to0$ as $s\to+\infty$, uniformly in $t$.
--
--   Then $(s,t)\mapsto A(s,t)-\sigma Ts-d$ and $(s,t)\mapsto W(s,t)-x(\sigma Tt+c)$ tend to $0$ in $C^\infty$: both are smooth on some $(s_0',\infty)\times\mathbb{R}$, and every derivative of each tends to $0$ uniformly in $t$.
--
--   This combines convergence up to a phase in all derivatives with uniform convergence at a fixed phase into $C^\infty$ convergence at that fixed phase, which is the form of the conclusion of asymptotic cylindricity.
--
--   **Formalization Note** Derivatives are `iteratedFDeriv ℝ` on $\mathbb{R}\times\mathbb{R}$ with the sup norm on $\mathbb{R}^{2n+2}$; the conclusion is `TendstoZeroCInfty` for both maps. In hypothesis 2, $x(\sigma T\,\cdot_2+c')$ is the map $(s,t)\mapsto x(\sigma Tt+c')$. $P$ may be multiply covered.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: Asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996), 337–379, with the Correction, ibid. 15 (1998), 535–538, proof of Theorem 1.3

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `P = (x, T)` be a periodic Reeb orbit, `σ = ±1`, and `A : ℝ × ℝ → ℝ`, `W : ℝ × ℝ → V n`
smooth on some `(s₀, ∞) × ℝ`. Suppose every derivative of order `≥ 1` of `A(s, t) - σ T s` tends to
`0` uniformly in `t`; for every `m` and `ε > 0`, for all large `s` there is a phase `c'` such that
the derivatives of order `≤ m` of `W - x(σ T t + c')` at `(s, t)` are at most `ε` for all `t`; and
`A(s, t) - σ T s - d → 0`, `W(s, t) - x(σ T t + c) → 0` uniformly in `t`. Then both
`A(s, t) - σ T s - d` and `W(s, t) - x(σ T t + c)` tend to `0` in `C^∞`. -/
theorem tendstoZeroCInfty_of_tendstoZeroUnif_mod_phase {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (A : ℝ × ℝ → ℝ) (W : ℝ × ℝ → V n)
    (hsm : ∃ s₀ : ℝ, ContDiffOn ℝ ∞ A (Set.Ioi s₀ ×ˢ Set.univ) ∧
      ContDiffOn ℝ ∞ W (Set.Ioi s₀ ×ˢ Set.univ))
    (hA : ∀ m : ℕ, 1 ≤ m → ∀ ε > 0, ∃ s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => A p - σ * P.T * p.1) (s, t)‖ ≤ ε)
    (hW : ∀ m : ℕ, ∀ ε > 0, ∃ s₁ : ℝ, ∀ s ≥ s₁, ∃ c' : ℝ, ∀ j ≤ m, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ j (fun p : ℝ × ℝ => W p - P.x (σ * P.T * p.2 + c')) (s, t)‖ ≤ ε)
    (d c : ℝ) (hA0 : TendstoZeroUnif (fun p : ℝ × ℝ => A p - σ * P.T * p.1 - d))
    (hW0 : TendstoZeroUnif (fun p : ℝ × ℝ => W p - P.x (σ * P.T * p.2 + c))) :
    TendstoZeroCInfty (fun p : ℝ × ℝ => A p - σ * P.T * p.1 - d) ∧
      TendstoZeroCInfty (fun p : ℝ × ℝ => W p - P.x (σ * P.T * p.2 + c)) := by
  sorry

end FiniteEnergyPlane
