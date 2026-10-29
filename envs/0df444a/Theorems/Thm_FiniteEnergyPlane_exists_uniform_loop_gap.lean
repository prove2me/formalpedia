-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_uniform_loop_gap
-- name    : FiniteEnergyPlane.exists_uniform_loop_gap
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-28T23:57:24.766773+00:00
-- url     : https://prove2.me/theorems/57f7bb0e-49bf-4a4e-afdd-e117e480f460
-- title:
--   Uniform spectral gaps of the asymptotic loop operator
-- statement:
--   Let $S_\infty:\mathbb{R}\to\mathbb{R}^{2n\times2n}$ be a continuous, $1$-periodic loop of symmetric matrices, and let $A=-J_0\partial_t-S_\infty$ be the asymptotic operator acting on $1$-periodic loops in $\mathbb{R}^{2n}$.
--
--   For every $\delta>0$ there is $c>0$ with the following property. Every interval $[a,a+\delta]$ contains some $\lambda$ such that
--   $$c\int_0^1\|u(t)\|^2\,dt\ \le\ \int_0^1\big\|-J_0u'(t)-S_\infty(t)u(t)-\lambda u(t)\big\|^2\,dt$$
--   for every $C^1$, $1$-periodic loop $u:\mathbb{R}\to\mathbb{R}^{2n}$.
--
--   So the spectrum of $A$ has gaps of a fixed size in every window of length $\delta$, with a bound $\|(A-\lambda)u\|_{L^2}\ge\sqrt c\,\|u\|_{L^2}$ that is uniform in the position $a$ of the window. This is a uniform form of the discreteness of the spectrum of asymptotic operators (C. Wendl, *Lectures on Symplectic Field Theory*, 2026 notes, Section 3.5). It is meant for reuse wherever an estimate must hold at levels arbitrarily far out in the spectrum with constants independent of the level.
--
--   **Formalization Note** The loop is `Sinf` with `CauchyRiemannIndex.IsSymLoop Sinf` (continuous, `1`-periodic, symmetric values). The derivative of `u` is supplied as a continuous function `u'` with `HasDerivAt u (u' t) t` for all `t`, and matrices act through `Matrix.toEuclideanLin`. The constant `c` depends on `δ` only, not on `a`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, lecture notes, Humboldt-Universität zu Berlin (2026 version); earlier version arXiv:1612.01009, Section 3.5 (discreteness of the spectrum of asymptotic operators)

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Filter Topology
open scoped ContDiff

/-- Uniform spectral gaps of the asymptotic loop operator `A = -J₀ ∂ₜ - S∞`: for every `δ > 0`
there is `c > 0` such that every interval `[a, a + δ]` contains some `λ` with
`c ∫₀¹ ‖u‖² ≤ ∫₀¹ ‖(A - λ) u‖²` for all `C¹`, `1`-periodic loops `u`. -/
theorem exists_uniform_loop_gap {n : ℕ} (Sinf : ℝ → CauchyRiemannIndex.Mat n)
    (hSinf : CauchyRiemannIndex.IsSymLoop Sinf) (δ : ℝ) (hδ : 0 < δ) :
    ∃ c > 0, ∀ a : ℝ, ∃ l ∈ Set.Icc a (a + δ), ∀ u u' : ℝ → CauchyRiemannIndex.Vec n,
      (∀ t, HasDerivAt u (u' t) t) → Continuous u' → Function.Periodic u 1 →
      c * ∫ t in (0:ℝ)..1, ‖u t‖ ^ 2 ≤ ∫ t in (0:ℝ)..1,
        ‖-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ n) (u' t)) -
          Matrix.toEuclideanLin (Sinf t) (u t) - l • u t‖ ^ 2 := by
  sorry

end FiniteEnergyPlane
