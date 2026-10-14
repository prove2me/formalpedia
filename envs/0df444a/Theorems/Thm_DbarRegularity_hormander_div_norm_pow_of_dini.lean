-- Prove2me | Theorems.Thm_DbarRegularity_hormander_div_norm_pow_of_dini
-- name    : DbarRegularity.hormander_div_norm_pow_of_dini
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T19:41:01.154733+00:00
-- url     : https://prove2.me/theorems/34bb9376-c734-40e0-bdf0-8004735e8610
-- title:
--   Hörmander condition for Ω(x)/|x|^d with Ω homogeneous, bounded and Dini on the sphere
-- statement:
--   Let $d\ge1$ and let $\Omega:\mathbb{R}^d\to\mathbb{C}$ be homogeneous of degree $0$ ($\Omega(tx)=\Omega(x)$ for all $x$ and $t>0$), bounded by $M$ ($|\Omega(x)|\le M$ for all $x$), and such that
--   $$w(\delta)=\sup\{|\Omega(x)-\Omega(x')| : |x|=|x'|=1,\ |x-x'|\le\delta\}$$
--   satisfies the Dini condition $\int_0^1 w(\delta)\,\frac{d\delta}{\delta}<\infty$ (Stein, Chapter II, § 4.2, condition (25)). Then there is $H\in\mathbb{R}$ such that the kernel $K(x)=\Omega(x)/|x|^d$ satisfies
--   $$\int_{|x|\ge2|y|}|K(x-y)-K(x)|\,dx\;\le\;H\qquad\text{for every }y\ne0 .$$
--
--   **Formalization Note.** $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)` with `volume`. The integral is a lower Lebesgue integral `∫⁻` of `‖·‖ₑ` over `{x | 2 * ‖y‖ ≤ ‖x‖}`, bounded by `ENNReal.ofReal H`; no measurability of $\Omega$ is assumed. $|x|^d$ is `‖x‖ ^ d` cast to `ℂ` (so $K(0)=0$). $w$ and the Dini integral are written exactly as in the hypothesis of `DbarRegularity.homogeneousSingularIntegral_lp`. $H$ is chosen before $y$.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter II, § 4.2, Theorem 3, p. 39

import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace DbarRegularity

open MeasureTheory Set Metric
open scoped ENNReal

/-- Let `Ω` on `ℝ^d` (`d ≥ 1`) be homogeneous of degree `0`, bounded by `M`, with spherical modulus of
continuity `w` satisfying `∫₀¹ w(δ) / δ dδ < ∞`. Then the kernel `K(x) = Ω(x) / |x|^d` satisfies
`∫_{|x| ≥ 2|y|} |K(x - y) - K(x)| dx ≤ H` for all `y ≠ 0`, with `H` independent of `y`. -/
theorem hormander_div_norm_pow_of_dini {d : ℕ} (hd : 0 < d) (Ω : EuclideanSpace ℝ (Fin d) → ℂ)
    (hhom : ∀ x, ∀ t : ℝ, 0 < t → Ω (t • x) = Ω x)
    (hdini : ∫⁻ δ in Set.Ioc (0 : ℝ) 1,
      (⨆ (x : EuclideanSpace ℝ (Fin d)) (x' : EuclideanSpace ℝ (Fin d)) (_ : ‖x‖ = 1)
        (_ : ‖x'‖ = 1) (_ : ‖x - x'‖ ≤ δ), ‖Ω x - Ω x'‖ₑ) / ENNReal.ofReal δ < ⊤)
    (M : ℝ) (hM : ∀ x, ‖Ω x‖ ≤ M) :
    ∃ H : ℝ, ∀ y : EuclideanSpace ℝ (Fin d), y ≠ 0 →
      ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖},
        ‖Ω (x - y) / ((‖x - y‖ ^ d : ℝ) : ℂ) - Ω x / ((‖x‖ ^ d : ℝ) : ℂ)‖ₑ
        ≤ ENNReal.ofReal H := by sorry

end DbarRegularity
