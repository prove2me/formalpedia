-- Prove2me | Theorems.Thm_FiniteEnergyPlane_cylEnd_tendsto_of_loops_tendstoUnif_mod_phase
-- name    : FiniteEnergyPlane.cylEnd_tendsto_of_loops_tendstoUnif_mod_phase
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T09:05:28.202519+00:00
-- url     : https://prove2.me/theorems/c72993e8-b71d-4f40-8c44-d343a764039d
-- title:
--   Convergence on a cylindrical end from uniform convergence of loops up to phase
-- statement:
--   Let $u$ be a finite-energy $\tilde J$-holomorphic curve on $D\setminus\{0\}$ (strictly star-shaped level $S=H^{-1}(1)$, compatible $J$), $P=(x,T)$ a periodic Reeb orbit and $\sigma=\pm1$. Suppose that for every $\epsilon>0$ and all sufficiently small $r>0$ there is a phase $c'$ (depending on $r$) with $\|\mathrm{proj}\,u(re^{-2\pi it})-x(\sigma Tt+c')\|\le\epsilon$ for all $t$. Let $a(s,t)$ and $w(s,t)$ be the $\mathbb{R}$- and $S$-components of $u(e^{-2\pi(s+it)})$. Then
--
--   - $a$ and $w$ are smooth on some $(s_0,\infty)\times\mathbb{R}$;
--   - every derivative of order $\ge1$ of $a(s,t)-\sigma Ts$ tends to $0$ uniformly in $t$ as $s\to+\infty$;
--   - for every $m$ and $\epsilon>0$, for all large $s$ there is a phase $c'$ with $\|D^j\big(w-x(\sigma T\,\cdot+c')\big)(s,t)\|\le\epsilon$ for all $j\le m$ and all $t$.
--
--   Only $C^0$ closeness of the loops is assumed; no nondegeneracy of $P$ is required.
--
--   **Formalization Note** The loops are `loopInS H u (cwLoop 0 r)`; $a$, $w$ are `endA H u cylEnd`, `endW H u cylEnd`; derivatives are `iteratedFDeriv` on $\mathbb{R}^2$.
-- source:
--   Used for U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorem 2.11 and Lemma 2.12; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996)

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Convergence on the cylindrical end from `C⁰` convergence of the loops up to phase. Let `u` be a
finite-energy curve on `D \ {0}` and suppose that, as `r → 0⁺`, the loops
`t ↦ proj H (u (r e^{-2πit}))` become uniformly `ε`-close to some phase shift
`t ↦ x(σTt + c')` of the Reeb orbit `P` (the phase `c'` may depend on `r`). Then `a = endA` and
`w = endW` are smooth on some `(s₀, ∞) × ℝ`, all derivatives of order `≥ 1` of `a(s, t) - σTs`
tend to `0` uniformly, and for every `m` and `ε > 0`, for all large `s` there is a phase `c'`
with `D^j (w - x(σT · + c'))(s, t)` of norm `≤ ε` for all `j ≤ m` and all `t`. -/
theorem cylEnd_tendsto_of_loops_tendstoUnif_mod_phase {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1)
    (hloop : ∀ ε : ℝ, 0 < ε → ∀ᶠ r in 𝓝[>] (0 : ℝ), ∃ c' : ℝ, ∀ t : ℝ,
      ‖loopInS H u (cwLoop 0 r) t - P.x (σ * P.T * t + c')‖ ≤ ε) :
    (∃ s₀ : ℝ, ContDiffOn ℝ ∞ (endA H u cylEnd) (Set.Ioi s₀ ×ˢ Set.univ) ∧
        ContDiffOn ℝ ∞ (endW H u cylEnd) (Set.Ioi s₀ ×ˢ Set.univ)) ∧
      (∀ m : ℕ, 1 ≤ m → ∀ ε > 0, ∃ s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
        ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => endA H u cylEnd p - σ * P.T * p.1) (s, t)‖ ≤ ε) ∧
      ∀ m : ℕ, ∀ ε > 0, ∃ s₁ : ℝ, ∀ s ≥ s₁, ∃ c' : ℝ, ∀ j ≤ m, ∀ t : ℝ,
        ‖iteratedFDeriv ℝ j
          (fun p : ℝ × ℝ => endW H u cylEnd p - P.x (σ * P.T * p.2 + c')) (s, t)‖ ≤ ε := by
  sorry

end FiniteEnergyPlane
