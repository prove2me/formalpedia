-- Prove2me | Theorems.Thm_CellProbeTree_Matching_theorem_3_2
-- name    : CellProbeTree.Matching.theorem_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:35:47.607249+00:00
-- url     : https://prove2.me/theorems/0ca9917a-67af-40f2-8432-2f8663dcd413
-- title:
--   Theorem 3.2 — Talagrand's convex-distance inequality in the $d_T$ form: $\int e^{d_T(y,A)^2/4}\,dQ \le 1/Q(A)$
-- statement:
--   Let $\Omega = \prod_{c\in I}\Omega_c$ be a product of finitely many finite spaces, each $\Omega_c$ carrying a probability measure $\mu_c$, and let $Q = \bigotimes_c \mu_c$ be the product measure. Let $A \subseteq \Omega$ be nonempty with $Q(A) > 0$, and let $d_T(y, A)$ be Talagrand's convex distance (9). Then
--   $$\int_\Omega \exp\!\big(d_T(y,A)^2/4\big)\,dQ(y) \;\le\; \frac{1}{Q(A)},$$
--   and consequently, for every $\rho > 0$,
--   $$Q\{y : d_T(y,A) > \rho\} \;\le\; \frac{e^{-\rho^2/4}}{Q(A)}.$$
--   In the paper the inequality is applied with $\Omega = (\{0,1\}^w)^s$ (a coordinate is a whole memory word) and $Q$ uniform, to bound how far the actual memory is from a set of compatible memories.
--
--   Differences from the source:
--   - reading: "a finite product space with product measure $Q$" → finitely many coordinates, each a finite type with measurable singletons and an arbitrary probability measure, $Q$ = `Measure.pi μ`; reason: the paper's space $(\{0,1\}^w)^s$ is of this kind, and with finite coordinates every set (in particular every super-level set of $d_T$) is measurable.
--   - encoding: the integral of the nonnegative function $e^{d_T^2/4}$ and the bounds $1/Q(A)$, $e^{-\rho^2/4}/Q(A)$ → lower Lebesgue integral and division in $[0,\infty]$; reason: Lean convention for nonnegative integrals; the same value on a finite space.
-- source:
--   Liang, Liu, Nearly Tight Cell-Probe Lower Bounds for Querying on Tree via Talagrand Inequality, STOC 2027 submission (manuscript sha256 0e5a8eb2…), p. 12, Theorem 3.2 and equation (9)

import Mathlib
import Definitions.Def_CellProbeTree_Matching_ConvexDistance

open MeasureTheory

namespace CellProbeTree.Matching

/-- Theorem 3.2 (Talagrand), in the sup–inf form `d_T` of (9): on a finite product of finite
spaces with a product probability measure `Q`, for every nonempty `A` with `Q(A) > 0`,
`∫ exp(d_T(y, A)²/4) dQ(y) ≤ 1/Q(A)`, and `Q{d_T(·, A) > ρ} ≤ e^{−ρ²/4}/Q(A)` for every `ρ > 0`. -/
theorem theorem_3_2 {ι : Type*} [Fintype ι] {Ω : ι → Type*} [∀ c, Fintype (Ω c)]
    [∀ c, MeasurableSpace (Ω c)] [∀ c, MeasurableSingletonClass (Ω c)]
    (μ : ∀ c, Measure (Ω c)) [∀ c, IsProbabilityMeasure (μ c)]
    (A : Set (∀ c, Ω c)) (hA : A.Nonempty) (hQA : 0 < Measure.pi μ A) :
    (∫⁻ y, ENNReal.ofReal (Real.exp (convexDistance y A ^ 2 / 4)) ∂(Measure.pi μ)
        ≤ (Measure.pi μ A)⁻¹) ∧
      ∀ ρ : ℝ, 0 < ρ →
        Measure.pi μ {y | ρ < convexDistance y A}
          ≤ ENNReal.ofReal (Real.exp (-ρ ^ 2 / 4)) / Measure.pi μ A := by sorry

end CellProbeTree.Matching
