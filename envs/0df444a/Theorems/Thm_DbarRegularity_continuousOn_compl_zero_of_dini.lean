-- Prove2me | Theorems.Thm_DbarRegularity_continuousOn_compl_zero_of_dini
-- name    : DbarRegularity.continuousOn_compl_zero_of_dini
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T19:21:44.019984+00:00
-- url     : https://prove2.me/theorems/567e38b2-4bef-4350-b24f-b0df318092d0
-- title:
--   Degree-zero homogeneous functions with a Dini spherical modulus are continuous off the origin
-- statement:
--   Let $\Omega:\mathbb{R}^d\to\mathbb{C}$ be homogeneous of degree $0$ ($\Omega(tx)=\Omega(x)$ for all $x$ and $t>0$), and let
--   $$w(\delta)=\sup\{|\Omega(x)-\Omega(x')| : |x|=|x'|=1,\ |x-x'|\le\delta\}\in[0,\infty]$$
--   satisfy the Dini condition $\int_0^1 w(\delta)\,\frac{d\delta}{\delta}<\infty$ (condition (25) of Stein, Chapter II, § 4.2). Then $\Omega$ is continuous on $\mathbb{R}^d\setminus\{0\}$.
--
--   **Formalization Note.** $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)`; the conclusion is `ContinuousOn Ω {0}ᶜ`. The Dini hypothesis is copied verbatim from `DbarRegularity.homogeneousSingularIntegral_lp`: the iterated supremum in `ℝ≥0∞` of `‖Ω x - Ω x'‖ₑ`, divided by `ENNReal.ofReal δ`, integrated (lower Lebesgue integral) over `Set.Ioc 0 1`.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter II, § 4.2, Theorem 3, p. 39

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace DbarRegularity

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

/-- A function `Ω` on `ℝ^d`, homogeneous of degree `0`, whose spherical modulus of continuity
satisfies the Dini condition `∫₀¹ w(δ) / δ dδ < ∞`, is continuous on `ℝ^d \ {0}`. -/
theorem continuousOn_compl_zero_of_dini {d : ℕ} (Ω : EuclideanSpace ℝ (Fin d) → ℂ)
    (hhom : ∀ x, ∀ t : ℝ, 0 < t → Ω (t • x) = Ω x)
    (hdini : ∫⁻ δ in Set.Ioc (0 : ℝ) 1,
      (⨆ (x : EuclideanSpace ℝ (Fin d)) (x' : EuclideanSpace ℝ (Fin d)) (_ : ‖x‖ = 1)
        (_ : ‖x'‖ = 1) (_ : ‖x - x'‖ ≤ δ), ‖Ω x - Ω x'‖ₑ) / ENNReal.ofReal δ < ⊤) :
    ContinuousOn Ω {0}ᶜ := by sorry

end DbarRegularity
