-- Prove2me | Theorems.Thm_DbarRegularity_exists_norm_le_of_dini
-- name    : DbarRegularity.exists_norm_le_of_dini
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T19:23:38.721034+00:00
-- url     : https://prove2.me/theorems/ed12f639-6674-4c2a-9fcc-7eb9f13be3db
-- title:
--   Degree-zero homogeneous functions with a Dini spherical modulus are bounded
-- statement:
--   Let $\Omega:\mathbb{R}^d\to\mathbb{C}$ be homogeneous of degree $0$ ($\Omega(tx)=\Omega(x)$ for all $x$ and $t>0$), and let
--   $$w(\delta)=\sup\{|\Omega(x)-\Omega(x')| : |x|=|x'|=1,\ |x-x'|\le\delta\}\in[0,\infty]$$
--   satisfy the Dini condition $\int_0^1 w(\delta)\,\frac{d\delta}{\delta}<\infty$ (condition (25) of Stein, Chapter II, § 4.2). Then $\Omega$ is bounded: there is $M\in\mathbb{R}$ with $|\Omega(x)|\le M$ for all $x\in\mathbb{R}^d$.
--
--   **Formalization Note.** $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)`; the bound holds at every point, including $x=0$. The Dini hypothesis is copied verbatim from `DbarRegularity.homogeneousSingularIntegral_lp`: the iterated supremum in `ℝ≥0∞` of `‖Ω x - Ω x'‖ₑ`, divided by `ENNReal.ofReal δ`, integrated (lower Lebesgue integral) over `Set.Ioc 0 1`.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter II, § 4.2, Theorem 3, p. 39

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.ProperSpace

namespace DbarRegularity

open MeasureTheory Set Metric
open scoped ENNReal

/-- A function `Ω` on `ℝ^d`, homogeneous of degree `0`, whose spherical modulus of continuity
satisfies the Dini condition `∫₀¹ w(δ) / δ dδ < ∞`, is bounded. -/
theorem exists_norm_le_of_dini {d : ℕ} (Ω : EuclideanSpace ℝ (Fin d) → ℂ)
    (hhom : ∀ x, ∀ t : ℝ, 0 < t → Ω (t • x) = Ω x)
    (hdini : ∫⁻ δ in Set.Ioc (0 : ℝ) 1,
      (⨆ (x : EuclideanSpace ℝ (Fin d)) (x' : EuclideanSpace ℝ (Fin d)) (_ : ‖x‖ = 1)
        (_ : ‖x'‖ = 1) (_ : ‖x - x'‖ ≤ δ), ‖Ω x - Ω x'‖ₑ) / ENNReal.ofReal δ < ⊤) :
    ∃ M : ℝ, ∀ x, ‖Ω x‖ ≤ M := by sorry

end DbarRegularity
