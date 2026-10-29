-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_tendsto_of_upcrossing_levels
-- name    : FiniteEnergyPlane.exists_tendsto_of_upcrossing_levels
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-28T23:57:28.007123+00:00
-- url     : https://prove2.me/theorems/2556ead1-c688-4436-b87a-89021ad81a3b
-- title:
--   Convergence of a function that crosses levels of every scale only upward
-- statement:
--   Let $\alpha:\mathbb{R}\to\mathbb{R}$ have derivative $\alpha'(s)$ at every $s\ge s_0$, and let $\delta_0\in\mathbb{R}$. Assume:
--
--   1. for every $\delta>0$ there is $S$ such that every interval $[a,a+\delta]$ contains a level $\lambda$ with
--   $$s\ge S,\ \alpha(s)=\lambda\ \Longrightarrow\ \alpha'(s)>0 ;$$
--   2. for every $\mu>\delta_0$ there are arbitrarily large $s$ with $\alpha(s)<\mu$.
--
--   Then $\alpha(s)$ converges as $s\to\infty$ to a finite limit $\mu\le\delta_0$.
--
--   This is the real-variable step in the convergence of the slice Rayleigh quotient of a solution of a linear Cauchy–Riemann equation on a half-cylinder (C. Wendl, *Lectures on Symplectic Field Theory*, 2026 notes, Section 4.6). There, the levels in (1) come from spectral gaps of the asymptotic operator and (2) comes from a growth bound. The statement is purely about real functions and can be reused wherever a function can cross a dense family of levels only upward.
--
--   **Formalization Note** The derivative is given by `HasDerivAt α (α' s) s` for `s ≥ s₀`. Condition (1) is `∀ δ > 0, ∃ S, ∀ a, ∃ l ∈ Set.Icc a (a + δ), ∀ s ≥ S, α s = l → 0 < α' s`, and condition (2) is `∃ᶠ s in atTop, α s < μ` for each `μ > δ₀`. The conclusion is `Tendsto α atTop (𝓝 μ)` with `μ ≤ δ₀`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, lecture notes, Humboldt-Universität zu Berlin (2026 version), Section 4.6 (real-variable step in the convergence of the slice Rayleigh quotient)

import Mathlib

namespace FiniteEnergyPlane

open Filter Topology

/-- Let `α` be differentiable on `[s₀, ∞)` with derivative `α'`. Suppose that for every `δ > 0`
there is `S` such that every interval `[a, a + δ]` contains a level `λ` with `α' s > 0` whenever
`s ≥ S` and `α s = λ`, and that `α s < μ` for arbitrarily large `s` whenever `μ > δ₀`.
Then `α(s)` converges as `s → ∞` to a limit `μ ≤ δ₀`. -/
theorem exists_tendsto_of_upcrossing_levels (α α' : ℝ → ℝ) (s₀ δ₀ : ℝ)
    (hd : ∀ s ≥ s₀, HasDerivAt α (α' s) s)
    (hlev : ∀ δ > 0, ∃ S : ℝ, ∀ a : ℝ, ∃ l ∈ Set.Icc a (a + δ), ∀ s ≥ S, α s = l → 0 < α' s)
    (hup : ∀ μ > δ₀, ∃ᶠ s in atTop, α s < μ) :
    ∃ μ : ℝ, μ ≤ δ₀ ∧ Tendsto α atTop (𝓝 μ) := by
  sorry

end FiniteEnergyPlane
