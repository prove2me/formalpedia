-- Prove2me | Theorems.Thm_FiniteEnergyPlane_halfCyl_exp_decay_of_drift
-- name    : FiniteEnergyPlane.halfCyl_exp_decay_of_drift
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-30T16:11:23.068585+00:00
-- url     : https://prove2.me/theorems/4a626edd-b038-4c5b-8b34-366e8c0c446e
-- title:
--   Exponential decay on an end for Cauchy–Riemann equations asymptotic to a loop along a drifting phase
-- statement:
--   Let $J_0$ be the standard complex structure on $\mathbb{R}^{2n}$ and $S_\infty:\mathbb{R}\to\mathbb{R}^{2n\times2n}$ a smooth $1$-periodic loop of symmetric matrices whose asymptotic operator $-J_0\partial_t-S_\infty$ is nondegenerate. Let $s_1\in\mathbb{R}$ and let $S:\mathbb{R}^2\to\mathbb{R}^{2n\times2n}$ be smooth on $(s_1,\infty)\times\mathbb{R}$ with $S(s,t+1)=S(s,t)$ there. Let $\varphi:\mathbb{R}^2\to\mathbb{R}$ be a phase such that $\varphi(s,t)-t$ is smooth for large $s$ and every derivative of order $\ge1$ of $\varphi(s,t)-t$ tends to $0$ as $s\to+\infty$, uniformly in $t$ (no limit of $\varphi(s,t)-t$ is assumed). Suppose that each entry of
--   $$S(s,t)-S_\infty(\varphi(s,t))$$
--   tends to $0$ in $C^\infty$ as $s\to+\infty$. If $\zeta$ is smooth on $(s_1,\infty)\times\mathbb{R}$, $1$-periodic in $t$, solves $\partial_s\zeta+J_0\partial_t\zeta+S\zeta=0$ there, and $\zeta\to0$ uniformly in $t$, then there are $\delta>0$, $C$ and $s_2$ with $\|\zeta(s,t)\|\le Ce^{-\delta s}$ for $s\ge s_2$.
--
--   This is the form needed for the normal component of a pseudoholomorphic end in tube coordinates around a nondegenerate periodic Reeb orbit, before the convergence of the asymptotic phase is known. With a constant phase $\varphi(s,t)=t+c$ it reduces to `halfCyl_exp_decay_eventually` (8ec20b66).
--
--   **Formalization Note** "Tends to $0$ in $C^\infty$" is `TendstoZeroCInfty`; derivatives of $\varphi(s,t)-t$ are `iteratedFDeriv ℝ m (fun p => φ p - p.2)`. The equation is `CauchyRiemannIndex.crOp S ζ (s, t) = 0`.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996), Section 2

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Exponential decay for linear Cauchy–Riemann equations on an end `(s₁, ∞) × ℝ/ℤ` whose
coefficient is asymptotic to a nondegenerate loop along a drifting phase: if `S` is smooth and
`1`-periodic in `t` for `s > s₁`, `φ(s, t) - t` is smooth for large `s` with every derivative of
order `≥ 1` tending to `0` uniformly, `S(s, t) - S∞(φ(s, t)) → 0` in `C^∞`, the asymptotic operator
`-J₀ ∂ₜ - S∞` is nondegenerate, and the `1`-periodic smooth solution `ζ` of
`∂ₛζ + J₀ ∂ₜζ + S ζ = 0` on `s > s₁` tends to `0` uniformly, then `ζ` decays exponentially. -/
theorem halfCyl_exp_decay_of_drift {n : ℕ} (s₁ : ℝ) (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => S p i j) (Set.Ioi s₁ ×ˢ Set.univ))
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hnd : CauchyRiemannIndex.IsNondegenerate Sinf) (φ : ℝ × ℝ → ℝ)
    (hφs : ∃ s₂ : ℝ, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => φ p - p.2) (Set.Ioi s₂ ×ˢ Set.univ))
    (hφ : ∀ m : ℕ, 1 ≤ m → ∀ η > 0, ∃ s₂ : ℝ, ∀ s ≥ s₂, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => φ p - p.2) (s, t)‖ ≤ η)
    (hSas : ∀ i j, TendstoZeroCInfty (fun p : ℝ × ℝ => S p i j - Sinf (φ p) i j))
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : ContDiffOn ℝ ∞ ζ (Set.Ioi s₁ ×ˢ Set.univ))
    (hper : ∀ s > s₁, ∀ t : ℝ, S (s, t + 1) = S (s, t) ∧ ζ (s, t + 1) = ζ (s, t))
    (heq : ∀ s > s₁, ∀ t : ℝ, CauchyRiemannIndex.crOp S ζ (s, t) = 0)
    (hζ0 : TendstoZeroUnif ζ) :
    ∃ δ > 0, ∃ C s₂ : ℝ, ∀ s ≥ s₂, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (-(δ * s)) := by
  sorry

end FiniteEnergyPlane
