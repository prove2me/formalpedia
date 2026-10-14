-- Prove2me | Theorems.Thm_DbarRegularity_lintegral_Ici_comp_div_mul_inv
-- name    : DbarRegularity.lintegral_Ici_comp_div_mul_inv
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T19:31:29.453443+00:00
-- url     : https://prove2.me/theorems/b3e7d539-7dba-48b0-a4d3-d918d7ebb54f
-- title:
--   Inversion r = c/δ in a lower Lebesgue integral with weight dr/r
-- statement:
--   Let $c>0$ and let $w:\mathbb{R}\to[0,\infty]$ be any function. Then
--   $$\int_{r\ge c} w\!\left(\frac{c}{r}\right)\frac{dr}{r}\;=\;\int_{0<\delta\le1} w(\delta)\,\frac{d\delta}{\delta},$$
--   both sides being lower Lebesgue integrals with values in $[0,\infty]$.
--
--   **Formalization Note.** The integrals are `∫⁻` over `Ici c` and `Ioc 0 1` for Lebesgue measure; $1/r$ is `(ENNReal.ofReal r)⁻¹`. No measurability of $w$ is assumed.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter II, § 4.2, Theorem 3, p. 39

import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace DbarRegularity

open MeasureTheory Set
open scoped ENNReal

/-- For `c > 0` and any `w : ℝ → [0, ∞]`:
`∫_{r ≥ c} w(c / r) dr / r = ∫_{0 < δ ≤ 1} w(δ) dδ / δ`. -/
theorem lintegral_Ici_comp_div_mul_inv {c : ℝ} (hc : 0 < c) (w : ℝ → ℝ≥0∞) :
    ∫⁻ r in Ici c, w (c / r) * (ENNReal.ofReal r)⁻¹ =
      ∫⁻ δ in Ioc (0 : ℝ) 1, w δ * (ENNReal.ofReal δ)⁻¹ := by sorry

end DbarRegularity
