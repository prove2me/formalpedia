-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_tendsto_of_dbar_expDecay
-- name    : FiniteEnergyPlane.exists_tendsto_of_dbar_expDecay
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-30T10:56:19.074273+00:00
-- url     : https://prove2.me/theorems/ed03571f-eeb1-4b35-91c4-233032901cf3
-- title:
--   Convergence on a half-cylinder from an exponentially small Cauchy–Riemann defect
-- statement:
--   Let $f,g:\mathbb{R}^2\to\mathbb{R}$ be $C^1$ on $(s_0,\infty)\times\mathbb{R}$ and $1$-periodic in $t$ there, with $\partial_tf,\partial_tg\to0$ uniformly in $t$ as $s\to+\infty$. Suppose that for some $\delta>0$ and $C$,$$|\partial_sf-\partial_tg|+|\partial_tf+\partial_sg|\le Ce^{-\delta s}\qquad(s>s_0).$$Then $f$ and $g$ converge uniformly in $t$: there are constants $d,c\in\mathbb{R}$ with $f(s,t)-d\to0$ and $g(s,t)-c\to0$ as $s\to+\infty$, uniformly in $t$.
--
--   In other words, a function $f+ig$ on a half-cylinder whose $t$-derivative tends to $0$ and which is holomorphic up to an exponentially small error has a limit. No boundedness of $f$ or $g$ is assumed.
--
--   **Formalization Note** Partial derivatives are `fderiv ℝ _ (s, t) (1, 0)` and `fderiv ℝ _ (s, t) (0, 1)`; uniform convergence is `TendstoZeroUnif`.
-- source:
--   Used for H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: asymptotics (1996), Theorem 1.3

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `f, g : ℝ × ℝ → ℝ` be `C¹` on `(s₀, ∞) × ℝ` and `1`-periodic in `t` there, with
`∂ₜf, ∂ₜg → 0` uniformly in `t` as `s → +∞`. If the Cauchy–Riemann defect of `f + i g` decays
exponentially, `|∂ₛf - ∂ₜg| + |∂ₜf + ∂ₛg| ≤ C e^{-δs}` with `δ > 0`, then `f` and `g` converge
uniformly in `t`: there are constants `d, c` with `f - d → 0` and `g - c → 0` uniformly in `t`. -/
theorem exists_tendsto_of_dbar_expDecay (f g : ℝ × ℝ → ℝ) (s₀ : ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.Ioi s₀ ×ˢ Set.univ))
    (hg : ContDiffOn ℝ 1 g (Set.Ioi s₀ ×ˢ Set.univ))
    (hper : ∀ s > s₀, ∀ t : ℝ, f (s, t + 1) = f (s, t) ∧ g (s, t + 1) = g (s, t))
    (ht : ∀ η > 0, ∃ s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      |fderiv ℝ f (s, t) (0, 1)| ≤ η ∧ |fderiv ℝ g (s, t) (0, 1)| ≤ η)
    (δ C : ℝ) (hδ : 0 < δ)
    (hdbar : ∀ s > s₀, ∀ t : ℝ,
      |fderiv ℝ f (s, t) (1, 0) - fderiv ℝ g (s, t) (0, 1)| +
        |fderiv ℝ f (s, t) (0, 1) + fderiv ℝ g (s, t) (1, 0)| ≤ C * Real.exp (-(δ * s))) :
    ∃ d c : ℝ, TendstoZeroUnif (fun p : ℝ × ℝ => f p - d) ∧
      TendstoZeroUnif (fun p : ℝ × ℝ => g p - c) := by
  sorry

end FiniteEnergyPlane
