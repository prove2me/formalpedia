-- Prove2me | Theorems.Thm_FiniteEnergyPlane_halfCyl_exp_decay_of_shift_close
-- name    : FiniteEnergyPlane.halfCyl_exp_decay_of_shift_close
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-30T16:01:15.212984+00:00
-- url     : https://prove2.me/theorems/0582ea6f-c5c2-47a6-9465-05f4b8b98654
-- title:
--   Exponential decay for linear Cauchy–Riemann equations with a drifting asymptotic phase
-- statement:
--   Let $J_0$ be the standard complex structure on $\mathbb{R}^{2n}$ and $S_\infty:\mathbb{R}\to\mathbb{R}^{2n\times2n}$ a continuous $1$-periodic loop of symmetric matrices whose asymptotic operator $A=-J_0\partial_t-S_\infty$ on $1$-periodic loops is nondegenerate ($0$ is not an eigenvalue). Let $S:\mathbb{R}^2\to\mathbb{R}^{2n\times2n}$ be smooth with $S(s,t+1)=S(s,t)$, and suppose:
--   1. for every $\eta>0$ there is $s_1$ such that for every $s\ge s_1$ there is a phase $c=c(s)\in\mathbb{R}$ with $|S_{ij}(s,t)-S_{\infty,ij}(t+c)|\le\eta$ for all $t$ and all entries $i,j$;
--   2. the first and second $s$-derivatives $\partial_sS$, $\partial_s^2S$ tend to $0$ uniformly in $t$ as $s\to+\infty$.
--
--   If $\zeta:\mathbb{R}^2\to\mathbb{R}^{2n}$ is smooth on $(0,\infty)\times\mathbb{R}$, $1$-periodic in $t$, solves $\partial_s\zeta+J_0\partial_t\zeta+S\zeta=0$ for $s>0$, and $\zeta(s,t)\to0$ uniformly in $t$ as $s\to+\infty$, then there are $\delta>0$ and $C$ with
--   $$\|\zeta(s,t)\|\le Ce^{-\delta s}\qquad(s\ge1,\ t\in\mathbb{R}).$$
--
--   This generalizes `halfCyl_exp_decay` (81087bad), where $S(s,\cdot)\to S_\infty$ in $C^\infty$ with a fixed phase. Here the coefficient only approaches the family of phase shifts of $S_\infty$, and the phase $c(s)$ need not converge. This is the situation of an end of a pseudoholomorphic curve before the convergence of its asymptotic phase has been established.
--
--   **Formalization Note** The pure $s$-derivatives are written `iteratedFDeriv ℝ k (fun p => S p i j) (s, t) (fun _ => (1, 0))` for $k=1,2$. Nondegeneracy is `CauchyRiemannIndex.IsNondegenerate`, and the half-cylinder solution is `IsHalfCylSolution`.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996), Section 2; C. Wendl, Lectures on Symplectic Field Theory, Proposition 6.7.1

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Exponential decay for linear Cauchy–Riemann equations on a half-cylinder with a drifting
asymptotic phase: suppose `S` is smooth and `1`-periodic in `t`, that for every `η > 0` and all large
`s` the slice `S(s, ·)` is uniformly `η`-close to some phase shift `S∞(· + c)` of a nondegenerate
symmetric loop `S∞` (the shift `c` may depend on `s`), and that the first and second
`s`-derivatives of `S` tend to `0` uniformly. If the solution `ζ` of `∂ₛζ + J₀ ∂ₜζ + S ζ = 0`
tends to `0` uniformly, then `ζ` decays exponentially. -/
theorem halfCyl_exp_decay_of_shift_close {n : ℕ} (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j))
    (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hnd : CauchyRiemannIndex.IsNondegenerate Sinf)
    (hclose : ∀ η > 0, ∃ s₁ : ℝ, ∀ s ≥ s₁, ∃ c : ℝ, ∀ t : ℝ, ∀ i j,
      |S (s, t) i j - Sinf (t + c) i j| ≤ η)
    (hds : ∀ η > 0, ∃ s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ, ∀ i j,
      |iteratedFDeriv ℝ 1 (fun p => S p i j) (s, t) (fun _ => (1, 0))| ≤ η ∧
      |iteratedFDeriv ℝ 2 (fun p => S p i j) (s, t) (fun _ => (1, 0))| ≤ η)
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : IsHalfCylSolution S ζ)
    (hζ0 : TendstoZeroUnif ζ) :
    ∃ δ > 0, ∃ C : ℝ, ∀ s ≥ 1, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (-(δ * s)) := by
  sorry

end FiniteEnergyPlane
