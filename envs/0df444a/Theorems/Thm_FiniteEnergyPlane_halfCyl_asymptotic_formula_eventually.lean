-- Prove2me | Theorems.Thm_FiniteEnergyPlane_halfCyl_asymptotic_formula_eventually
-- name    : FiniteEnergyPlane.halfCyl_asymptotic_formula_eventually
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T09:05:31.355614+00:00
-- url     : https://prove2.me/theorems/d3cdffce-b702-42d2-aadb-893d1dc52030
-- title:
--   Asymptotic formula for linear Cauchy–Riemann equations on an end
-- statement:
--   Let $S:\mathbb{R}^2\to\mathbb{R}^{2n\times2n}$ be smooth and $1$-periodic in $t$ for $s>s_1$, $S_\infty$ a smooth symmetric loop with $S(s,t)-S_\infty(t)$ decaying like $e^{-ds}$ in $C^\infty$ ($d>0$). Let $\zeta$ be smooth and $1$-periodic in $t$ on $s>s_1$ with $\partial_s\zeta+J_0\partial_t\zeta+S\zeta=0$ there, not identically zero on any $[s_0,\infty)\times\mathbb{R}$, and $\|\zeta(s,t)\|\le Ce^{\delta_0s}$ for $s>s_1$. Then there are an eigenvalue $\mu\le\delta_0$ of $-J_0\partial_t-S_\infty$ and an eigenfunction $e$ with $$e^{-\mu s}\zeta(s,t)-e(t)\to0\quad\text{in }C^\infty,\text{ uniformly in }t,\text{ as }s\to+\infty.$$
--
--   This is the asymptotic formula for solutions given only on an end $(s_1,\infty)\times\mathbb{R}/\mathbb{Z}$; the operator $-J_0\partial_t-S_\infty$ may be degenerate.
--
--   **Formalization Note** `IsExpAsymptoticTo`, `IsLoopEigen` and `TendstoZeroCInfty` are from `FiniteEnergyPlane_Asymptotics`; nonvanishing is: for every $s_0$ there are $s\ge s_0$ and $t$ with $\zeta(s,t)\ne0$.
-- source:
--   Used for U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorem 2.11 and Lemma 2.12; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996)

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Asymptotic formula for linear Cauchy–Riemann equations on an end `(s₁, ∞) × ℝ/ℤ`, with data
given only there: let `S` be smooth and `1`-periodic in `t` for `s > s₁` with `S(s, t) - S∞(t)`
decaying like `e^{-ds}` in `C^∞` (`d > 0`, `S∞` a smooth symmetric loop), and let `ζ` be a smooth
`1`-periodic solution of `∂ₛζ + J₀ ∂ₜζ + S ζ = 0` on `s > s₁` which does not vanish identically
on any `[s₀, ∞) × ℝ` and satisfies `‖ζ(s, t)‖ ≤ C e^{δ₀ s}` for `s > s₁`. Then there are an
eigenvalue `μ ≤ δ₀` of `-J₀ ∂ₜ - S∞` and an eigenfunction `e` with `e^{-μs} ζ(s, t) - e(t) → 0`
in `C^∞`. -/
theorem halfCyl_asymptotic_formula_eventually {n : ℕ} (s₁ : ℝ)
    (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => S p i j) (Set.Ioi s₁ ×ˢ Set.univ))
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (d : ℝ) (hd : 0 < d) (hSas : IsExpAsymptoticTo S Sinf d)
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : ContDiffOn ℝ ∞ ζ (Set.Ioi s₁ ×ˢ Set.univ))
    (hper : ∀ s > s₁, ∀ t : ℝ, S (s, t + 1) = S (s, t) ∧ ζ (s, t + 1) = ζ (s, t))
    (heq : ∀ s > s₁, ∀ t : ℝ, CauchyRiemannIndex.crOp S ζ (s, t) = 0)
    (hne : ∀ s₀ : ℝ, ∃ s ≥ s₀, ∃ t : ℝ, ζ (s, t) ≠ 0)
    (C δ₀ : ℝ) (hgrowth : ∀ s > s₁, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (δ₀ * s)) :
    ∃ μ : ℝ, μ ≤ δ₀ ∧ ∃ e : ℝ → CauchyRiemannIndex.Vec n, IsLoopEigen Sinf μ e ∧
      TendstoZeroCInfty (fun p : ℝ × ℝ => Real.exp (-(μ * p.1)) • ζ p - e p.2) := by
  sorry

end FiniteEnergyPlane
