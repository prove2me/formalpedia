-- Prove2me | Theorems.Thm_FiniteEnergyPlane_halfCyl_slice_deriv_sq_le_of_logDeriv_bound
-- name    : FiniteEnergyPlane.halfCyl_slice_deriv_sq_le_of_logDeriv_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-28T22:42:58.061109+00:00
-- url     : https://prove2.me/theorems/41e13e5e-c065-4acf-a889-d9c873f26c2b
-- title:
--   Slice derivative bound for linear Cauchy–Riemann solutions with bounded $L^2$ growth rate
-- statement:
--   Let $S:\mathbb{R}\times\mathbb{R}\to\mathbb{R}^{2n\times2n}$ be smooth and $1$-periodic in $t$, and let $\zeta$ solve $\partial_s\zeta+J_0\partial_t\zeta+S\zeta=0$ on the half-cylinder $(0,\infty)\times\mathbb{R}/\mathbb{Z}$. Let $s_0>0$, $c$ and $\Lambda$ be such that for all $s\ge s_0$ and all $t$, the entries of $S(s,t)$, $\partial_sS(s,t)$ and $\partial_s^2S(s,t)$ are bounded in absolute value by $c$, and
--   $$\Big|\int_0^1\langle\zeta(s,t),\partial_s\zeta(s,t)\rangle\,dt\Big|\le\Lambda\int_0^1|\zeta(s,t)|^2\,dt.$$
--   Then there are $M$ and $s_1$ such that for all $s\ge s_1$,
--   $$\int_0^1|\partial_t\zeta(s,t)|^2\,dt\le M\int_0^1|\zeta(s,t)|^2\,dt.$$
--
--   The hypothesis says that the logarithmic derivative of the slice energy $\int_0^1|\zeta(s,\cdot)|^2$ is bounded. The conclusion bounds the $t$-derivative of each slice by the slice itself, uniformly for large $s$. It is used for `FiniteEnergyPlane.halfCyl_slice_deriv_sq_le` (Wendl, Lemma 4.8.8).
--
--   **Formalization Note** The solution is `IsHalfCylSolution S ζ`. The $s$-derivatives of $S$ and $\zeta$ are `fderiv … (s, t) (1, 0)`, and the $t$-derivative of the slice is `deriv (fun x => ζ (s, x)) t`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory (2026 notes), Lemma 4.8.8 (version with a bounded growth rate)

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real RealInnerProductSpace

/-- Let `ζ` solve `∂ₛζ + J₀ ∂ₜζ + S ζ = 0` on a half-cylinder, with smooth `1`-periodic `S` whose
entries and their first two `s`-derivatives are bounded for `s ≥ s₀`. If
`|⟨ζ, ∂ₛζ⟩_{L²}| ≤ Λ ‖ζ‖²_{L²}` on every slice `s ≥ s₀`, then for large `s` the `L²` norm of the
`t`-derivative of the slice `ζ(s, ·)` is bounded by a fixed multiple of the `L²` norm of the slice. -/
theorem halfCyl_slice_deriv_sq_le_of_logDeriv_bound {n : ℕ}
    (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j))
    (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : IsHalfCylSolution S ζ)
    (s₀ c Λ : ℝ) (hs₀ : 0 < s₀)
    (hSb : ∀ s ≥ s₀, ∀ t : ℝ, ∀ i j, |S (s, t) i j| ≤ c ∧
      |fderiv ℝ (fun p : ℝ × ℝ => S p i j) (s, t) (1, 0)| ≤ c ∧
      |fderiv ℝ (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => S q i j) p (1, 0)) (s, t) (1, 0)| ≤ c)
    (hα : ∀ s ≥ s₀, |∫ t in (0:ℝ)..1, ⟪ζ (s, t), fderiv ℝ ζ (s, t) (1, 0)⟫| ≤
      Λ * ∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2) :
    ∃ M s₁ : ℝ, ∀ s ≥ s₁,
      ∫ t in (0:ℝ)..1, ‖deriv (fun x => ζ (s, x)) t‖ ^ 2 ≤
        M * ∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2 := by
  sorry

end FiniteEnergyPlane
