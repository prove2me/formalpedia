-- Prove2me | Theorems.Thm_BalkemaDeHaan_Moments_tail_moment_identity
-- name    : BalkemaDeHaan.Moments.tail_moment_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:10:41.456585+00:00
-- url     : https://prove2.me/theorems/eac831d5-6c45-44b7-8c80-ebbeda697d4b
-- title:
--   Proof of Theorem 8(a), p. 803 — $\int_x^\infty y^\xi dF / (x^\xi(1-F(x))) = \xi\int_x^\infty y^{\xi-1}(1-F(y))dy / (x^\xi(1-F(x))) + 1$
-- statement:
--   Let $X$ be a real random variable with distribution function $F$ such that $F(x) < 1$ for every real $x$, and let $\xi > 0$ be such that $\int_0^\infty y^\xi\, dF(y)$ is finite. Then for every $x > 0$:
--
--   1. the function $y \mapsto y^{\xi - 1}(1 - F(y))$ is Lebesgue integrable on $(x, \infty)$;
--   2. the conditional moment is the normalized tail moment,
--   $$E\Big(\Big(\frac{X}{x}\Big)^{\xi}\,\Big|\,X > x\Big) = \frac{\int_x^\infty y^\xi\, dF(y)}{x^\xi(1-F(x))};$$
--   3. and
--   $$
--   \frac{\int_x^\infty y^\xi\, dF(y)}{x^\xi(1-F(x))} = \xi\,\frac{\int_x^\infty y^{\xi-1}(1-F(y))\, dy}{x^\xi(1-F(x))} + 1 .
--   $$
--
--   Here $\int_x^\infty \cdot\, dF$ integrates over the open half-line $(x,\infty)$, so that $1 - F(x) = P\{X > x\}$ is its total mass. The identity turns the conditional moment into a ratio of an integral of the tail $1-F$ to the tail itself, the form to which Karamata's theorem on integrals of regularly varying functions applies; this is how the paper reduces Theorem 8(a) to Karamata's theorem.
--
--   **Formalization Note** The finiteness of $\int_0^\infty y^\xi dF(y)$ is integrability of $y \mapsto y^\xi$ on $(0,\infty)$ for the law of $X$. Integrability of the $dy$-integrand is part of the conclusion, so the identity is not satisfied by Lean's junk value $0$ for a non-integrable Bochner integral.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 803 (PDF p. 12), proof of Theorem 8(a), displayed identity

import Mathlib
import Definitions.Def_BalkemaDeHaan_Moments_ResidualLife

open MeasureTheory

namespace BalkemaDeHaan.Moments

/-- Proof of Theorem 8(a), p. 803, the displayed identity: if `∫_0^∞ y^ξ dF(y) < ∞` (`ξ > 0`) and
`F(x) < 1` for all `x`, then for every `x > 0` the function `y ↦ y^{ξ−1}(1 − F(y))` is Lebesgue
integrable on `(x, ∞)`, the left side of the display is `E((X/x)^ξ | X > x)`, and
`∫_x^∞ y^ξ dF(y) / (x^ξ(1 − F(x))) = ξ ∫_x^∞ y^{ξ−1}(1 − F(y)) dy / (x^ξ(1 − F(x))) + 1`. -/
theorem tail_moment_identity (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hD₀ : ∀ x : ℝ, 0 < μ (Set.Ioi x))
    (ξ : ℝ) (hξ : 0 < ξ)
    (hmom : IntegrableOn (fun y : ℝ => y ^ ξ) (Set.Ioi 0) μ)
    (x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun y : ℝ => y ^ (ξ - 1) * BalkemaDeHaan.LimitTypes.tail μ y) (Set.Ioi x) ∧
    condMoment μ ξ x = (∫ y in Set.Ioi x, y ^ ξ ∂μ) / (x ^ ξ * BalkemaDeHaan.LimitTypes.tail μ x) ∧
    (∫ y in Set.Ioi x, y ^ ξ ∂μ) / (x ^ ξ * BalkemaDeHaan.LimitTypes.tail μ x) =
      ξ * (∫ y in Set.Ioi x, y ^ (ξ - 1) * BalkemaDeHaan.LimitTypes.tail μ y) / (x ^ ξ * BalkemaDeHaan.LimitTypes.tail μ x) + 1 := by sorry

end BalkemaDeHaan.Moments
