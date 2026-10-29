-- Prove2me | Theorems.Thm_FiniteEnergyPlane_halfCyl_slice_deriv_sq_le
-- name    : FiniteEnergyPlane.halfCyl_slice_deriv_sq_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-28T21:24:10.498181+00:00
-- url     : https://prove2.me/theorems/96497da3-ebff-42a6-ad0b-2f0aef243806
-- title:
--   Slice derivative bound for linear Cauchy–Riemann solutions on a half-cylinder
-- statement:
--   Let $S:\mathbb{R}^2\to\mathbb{R}^{2n\times2n}$ be $C^\infty$ and $1$-periodic in $t$. Let $S_\infty$ be a $C^\infty$, $1$-periodic loop of symmetric matrices with $S\to S_\infty$ in $C^\infty$. Let $\zeta$ be a solution of $\partial_s\zeta+J_0\partial_t\zeta+S\zeta=0$ on the half-cylinder. Assume $\zeta$ is not identically zero on $(0,\infty)\times\mathbb{R}$ and satisfies $\|\zeta(s,t)\|\le Ce^{\delta_0s}$ for $s>0$. Put $F(s)=\int_0^1\|\zeta(s,t)\|^2\,dt$.
--
--   Then there are constants $M$ and $s_1$ such that for all $s\ge s_1$
--   $$\int_0^1\|\partial_t\zeta(s,t)\|^2\,dt\;\le\;M\,F(s).$$
--
--   This is a uniform slice estimate for such solutions (C. Wendl, *Lectures on Symplectic Field Theory*, 2026 notes, Lemma 4.8.8). It is used for `FiniteEnergyPlane.halfCyl_exists_subseq_tendsto_eigen`.
--
--   **Formalization Note** No rate of convergence of $S$ and no nondegeneracy of $S_\infty$ is assumed. $\partial_t\zeta(s,t)$ is `deriv (fun x => ζ (s, x)) t`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, lecture notes, Humboldt-Universität zu Berlin (2026 version); earlier version arXiv:1612.01009, Theorem 4.8.2 and Lemmas 4.8.8, 4.8.11

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A solution of `∂ₛζ + J₀ ∂ₜζ + S ζ = 0` on a half-cylinder, with `S(s, t) → S∞(t)` in `C^∞`,
not identically zero and with `‖ζ(s, t)‖ ≤ C e^{δ₀ s}`: for large `s`, the `L²` norm of the
`t`-derivative of the slice `ζ(s, ·)` is bounded by a fixed multiple of the `L²` norm of the
slice. -/
theorem halfCyl_slice_deriv_sq_le {n : ℕ} (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j)) (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hSas : IsCInftyAsymptoticTo S Sinf)
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : IsHalfCylSolution S ζ)
    (hne : ∃ p : ℝ × ℝ, 0 < p.1 ∧ ζ p ≠ 0)
    (C δ₀ : ℝ) (hgrowth : ∀ s > 0, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (δ₀ * s)) :
    ∃ M s₁ : ℝ, ∀ s ≥ s₁,
      ∫ t in (0:ℝ)..1, ‖deriv (fun x => ζ (s, x)) t‖ ^ 2 ≤ M * ∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2 := by
  sorry

end FiniteEnergyPlane
