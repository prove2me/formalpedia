-- Prove2me | Theorems.Thm_DbarRegularity_exists_modulus_lt_of_dini
-- name    : DbarRegularity.exists_modulus_lt_of_dini
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T19:18:56.682991+00:00
-- url     : https://prove2.me/theorems/07e10989-4be7-47df-87e8-0a9926541382
-- title:
--   A Dini-integrable spherical modulus of continuity tends to zero
-- statement:
--   Let $\Omega:\mathbb{R}^d\to\mathbb{C}$ be any function and let
--   $$w(\delta)=\sup\{|\Omega(x)-\Omega(x')| : |x|=|x'|=1,\ |x-x'|\le\delta\}\in[0,\infty]$$
--   be its modulus of continuity on the unit sphere. If $\int_0^1 w(\delta)\,\frac{d\delta}{\delta}<\infty$ (the Dini condition (25) of Stein, Chapter II, § 4.2), then for every $\varepsilon>0$ there is $\delta>0$ with $w(\delta)<\varepsilon$.
--
--   This is the uniform continuity of $\Omega$ on the unit sphere that the Dini condition provides; it is used to show that such $\Omega$ is continuous away from the origin and bounded.
--
--   **Formalization Note.** $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)`; $w(\delta)$ is the iterated supremum in `ℝ≥0∞` of `‖Ω x - Ω x'‖ₑ`, exactly as in the hypothesis of `DbarRegularity.homogeneousSingularIntegral_lp`. The Dini integral is the lower Lebesgue integral over `Set.Ioc 0 1` of `w δ / ENNReal.ofReal δ`. No measurability of $\Omega$ is assumed.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter II, § 4.2, Theorem 3, p. 39

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace DbarRegularity

open MeasureTheory Set
open scoped ENNReal

/-- If the modulus of continuity `w(δ) = sup {|Ω(x) - Ω(x')| : |x| = |x'| = 1, |x - x'| ≤ δ}` of a
function `Ω` on the unit sphere of `ℝ^d` satisfies `∫₀¹ w(δ) / δ dδ < ∞`, then `w(δ)` becomes
arbitrarily small for small `δ > 0`. -/
theorem exists_modulus_lt_of_dini {d : ℕ} (Ω : EuclideanSpace ℝ (Fin d) → ℂ)
    (hdini : ∫⁻ δ in Set.Ioc (0 : ℝ) 1,
      (⨆ (x : EuclideanSpace ℝ (Fin d)) (x' : EuclideanSpace ℝ (Fin d)) (_ : ‖x‖ = 1)
        (_ : ‖x'‖ = 1) (_ : ‖x - x'‖ ≤ δ), ‖Ω x - Ω x'‖ₑ) / ENNReal.ofReal δ < ⊤)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ (⨆ (x : EuclideanSpace ℝ (Fin d)) (x' : EuclideanSpace ℝ (Fin d))
        (_ : ‖x‖ = 1) (_ : ‖x'‖ = 1) (_ : ‖x - x'‖ ≤ δ), ‖Ω x - Ω x'‖ₑ) < ENNReal.ofReal ε := by sorry

end DbarRegularity
