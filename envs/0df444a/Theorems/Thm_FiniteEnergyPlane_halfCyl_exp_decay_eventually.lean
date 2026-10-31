-- Prove2me | Theorems.Thm_FiniteEnergyPlane_halfCyl_exp_decay_eventually
-- name    : FiniteEnergyPlane.halfCyl_exp_decay_eventually
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-29T21:53:31.597735+00:00
-- url     : https://prove2.me/theorems/8ec20b66-7c12-4566-8cdb-5a73cb4c2e6c
-- title:
--   Exponential decay for linear Cauchy–Riemann equations on an end of a cylinder
-- statement:
--   Let $s_1\in\mathbb{R}$, let $S(s,t)$ be real $2n\times2n$ matrices depending smoothly on $(s,t)\in(s_1,\infty)\times\mathbb{R}$ and $1$-periodic in $t$ there, and let $S_\infty$ be a smooth $1$-periodic loop of symmetric matrices with $S(s,t)\to S_\infty(t)$ in $C^\infty$, uniformly in $t$, as $s\to+\infty$. Suppose the asymptotic operator $-J_0\partial_t-S_\infty$ is nondegenerate. Let $\zeta:\mathbb{R}^2\to\mathbb{R}^{2n}$ be smooth on $(s_1,\infty)\times\mathbb{R}$, $1$-periodic in $t$ there, with$$\partial_s\zeta+J_0\partial_t\zeta+S\zeta=0\qquad(s>s_1),$$and $\zeta(s,t)\to0$ uniformly in $t$. Then $\zeta$ decays exponentially: there are $\delta>0$, $C$ and $s_2$ with $\|\zeta(s,t)\|\le Ce^{-\delta s}$ for all $s\ge s_2$ and all $t$.
--
--   This is the exponential decay statement for linear Cauchy–Riemann equations on a half-cylinder in the form in which it is applied on an end, where the equation and its coefficients are only given for $s$ beyond some $s_1$.
--
--   **Formalization Note** $C^\infty$ convergence of matrices is entrywise `IsCInftyAsymptoticTo`; uniform convergence is `TendstoZeroUnif`. `Mat n` and `Vec n` are $2n\times2n$ real matrices and $\mathbb{R}^{2n}$, `crOp S ζ` is $\partial_s\zeta+J_0\partial_t\zeta+S\zeta$, a loop of symmetric matrices is `IsSymLoop` (continuous, $1$-periodic, symmetric), and nondegeneracy of $-J_0\partial_t-S_\infty$ is `CauchyRiemannIndex.IsNondegenerate` ($1$ is not an eigenvalue of the time-$1$ map $\Psi(1)$ of $\Psi'=J_0S_\infty\Psi$, $\Psi(0)=1$).
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory (2026 notes), Proposition 6.7.1; H. Hofer, K. Wysocki, E. Zehnder, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996)

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Exponential decay for linear Cauchy–Riemann equations on an end `(s₁, ∞) × ℝ/ℤ`, with data
given only there: if `S` is smooth and `1`-periodic in `t` for `s > s₁`, `S(s, t) → S∞(t)` in
`C^∞`, the asymptotic operator `-J₀ ∂ₜ - S∞` is nondegenerate, and the `1`-periodic smooth
solution `ζ` of `∂ₛζ + J₀ ∂ₜζ + S ζ = 0` on `s > s₁` tends to `0` uniformly, then `ζ` decays
exponentially. -/
theorem halfCyl_exp_decay_eventually {n : ℕ} (s₁ : ℝ) (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => S p i j) (Set.Ioi s₁ ×ˢ Set.univ))
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hSas : IsCInftyAsymptoticTo S Sinf) (hnd : CauchyRiemannIndex.IsNondegenerate Sinf)
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : ContDiffOn ℝ ∞ ζ (Set.Ioi s₁ ×ˢ Set.univ))
    (hper : ∀ s > s₁, ∀ t : ℝ, S (s, t + 1) = S (s, t) ∧ ζ (s, t + 1) = ζ (s, t))
    (heq : ∀ s > s₁, ∀ t : ℝ, CauchyRiemannIndex.crOp S ζ (s, t) = 0)
    (hζ0 : TendstoZeroUnif ζ) :
    ∃ δ > 0, ∃ C s₂ : ℝ, ∀ s ≥ s₂, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (-(δ * s)) := by
  sorry

end FiniteEnergyPlane
