-- Prove2me | Theorems.Thm_BalkemaDeHaan_Moments_gamma_moment
-- name    : BalkemaDeHaan.Moments.gamma_moment
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:09:45.842987+00:00
-- url     : https://prove2.me/theorems/919b9f6d-7fca-401a-82a2-cb0219f1f552
-- title:
--   Theorem 8(a), p. 803 — $c = \int_0^\infty x^\xi\, d\Gamma_\alpha(x-1) = (1-\xi/\alpha)^{-1}$
-- statement:
--   Let $0 < \xi < \alpha$. There is a probability measure on $\mathbb R$ whose distribution function is $x \mapsto \Gamma_\alpha(x-1)$ (that is, $1 - x^{-\alpha}$ for $x \ge 1$ and $0$ for $x < 1$), and for every such probability measure $\nu$ the $\xi$-th moment on $(0,\infty)$ is finite and
--
--   $$
--   \int_0^\infty x^\xi \, d\Gamma_\alpha(x-1) = \Big(1 - \frac{\xi}{\alpha}\Big)^{-1}.
--   $$
--
--   This identifies the value of the limit $c = \lim_{t\to\infty} E((X/t)^\xi \mid X > t)$ in Theorem 8(a): it is the $\xi$-th moment of the limit law of $X/t$ given $X > t$.
--
--   **Formalization Note** The Stieltjes integral $\int x^\xi d\Gamma_\alpha(x-1)$ is the Lebesgue integral against the probability measure whose distribution function (`ProbabilityTheory.cdf`) is $x \mapsto \Gamma_\alpha(x-1)$. A distribution function determines its law, so the statement quantifies over all such measures and also asserts that one exists, so that it is not vacuous.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 803 (PDF p. 12), Theorem 8(a), last sentence

import Mathlib
import Definitions.Def_BalkemaDeHaan_ParetoBounds_GammaLaw

open MeasureTheory ProbabilityTheory

namespace BalkemaDeHaan.Moments

/-- Theorem 8(a), p. 803, "Then c = ∫_0^∞ x^ξ dΓ_α(x − 1) = (1 − ξ/α)^{−1}": for `0 < ξ < α`,
there is a probability law on `ℝ` whose distribution function is `x ↦ Γ_α(x − 1)`, and every such
law `ν` has a finite `ξ`-th moment on `(0, ∞)` equal to `(1 − ξ/α)^{−1}`. -/
theorem gamma_moment (α ξ : ℝ) (hξ : 0 < ξ) (hξα : ξ < α) :
    (∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ∀ x : ℝ, cdf ν x = BalkemaDeHaan.ParetoBounds.GammaLaw α (x - 1)) ∧
    ∀ ν : Measure ℝ, IsProbabilityMeasure ν → (∀ x : ℝ, cdf ν x = BalkemaDeHaan.ParetoBounds.GammaLaw α (x - 1)) →
      IntegrableOn (fun x : ℝ => x ^ ξ) (Set.Ioi 0) ν ∧
      ∫ x in Set.Ioi 0, x ^ ξ ∂ν = (1 - ξ / α)⁻¹ := by sorry

end BalkemaDeHaan.Moments
