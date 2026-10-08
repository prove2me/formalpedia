-- Prove2me | Theorems.Thm_CorreaThreshold_Nonadaptive_expected_max_eq_sum
-- name    : CorreaThreshold.Nonadaptive.expected_max_eq_sum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:37:17.966958+00:00
-- url     : https://prove2.me/theorems/8a7733ce-1f9a-4475-bcc5-dc380549d446
-- title:
--   Proof of Theorem 1, p. 1460 — decompose E[max_i X_i] by its maximizer
-- statement:
--   Let $X_1,\ldots,X_n$ be independent, almost surely nonnegative, atomless random variables. If $A_i$ is the event that $X_i$ is at least every $X_j$, then ties have probability zero and
--
--   $$\mathbb E\!\left[\max_i X_i\right]=\sum_i\mathbb E[X_i\mathbf1_{A_i}].$$
--
--   This is the paper's decomposition of the prophet's expected maximum before the comparison with threshold-tail rewards.
--
--   **Formalization Note** The formula is integrated in $[0,\infty]$ and thus includes infinite expectations. The atomless assumption is the proof's continuous-distribution case. Nonnegativity is almost sure, and the variables are indexed from zero in Lean.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), pp. 1459–1460, proof of Theorem 1; https://doi.org/10.1287/moor.2020.1105

import Mathlib
import Definitions.Def_CorreaThreshold_Nonadaptive_Setting

namespace CorreaThreshold.Nonadaptive

open MeasureTheory ProbabilityTheory

/-- The maximum is the sum of the prizes on the unique-maximizer events. -/
theorem expected_max_eq_sum {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} [NeZero n]
    (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hXnn : ∀ i, ∀ᵐ ω ∂P, 0 ≤ X i ω)
    (hind : iIndepFun X P)
    (hcont : ∀ i, ∀ x : ℝ, P {ω | X i ω = x} = 0) :
    (∫⁻ ω, ENNReal.ofReal (SamuelCahnProphet.Median.maxX X ω) ∂P) =
      ∑ i : Fin n, ∫⁻ ω,
        (if ∀ j, X j ω ≤ X i ω then ENNReal.ofReal (X i ω) else 0) ∂P := by sorry

end CorreaThreshold.Nonadaptive
