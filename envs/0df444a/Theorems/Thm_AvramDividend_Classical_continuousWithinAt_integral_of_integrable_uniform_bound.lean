-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuousWithinAt_integral_of_integrable_uniform_bound
-- name    : AvramDividend.Classical.continuousWithinAt_integral_of_integrable_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:09:18.343907+00:00
-- url     : https://prove2.me/theorems/004141f3-a12d-418f-9d33-4c4fd1f9a2d7
-- title:
--   Continuity of parameterised Lévy integrals from a uniform integrable domination
-- statement:
--   Given a real state interval s, a measurable jump increment F(x,y), one integrable upper bound uniform over states in s, and almost-everywhere continuity of F as a function of x at x0 in s, the integrated function x↦∫F(x,y)dμ(y) is continuous within s at x0. Uses the dominated-convergence theorem for the nhdsWithin filter. This is the continuity step needed to upgrade almost-everywhere generator q-harmonicity to a pointwise result under localised Lévy domination.
-- source:
--   Pinned Mathlib MeasureTheory.tendsto_integral_filter_of_dominated_convergence; compact compensated-generator domination for Avram Dividend.

import Mathlib

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem continuousWithinAt_integral_of_integrable_uniform_bound
    (μ : Measure ℝ) (s : Set ℝ) (F : ℝ → ℝ → ℝ)
    (bound : ℝ → ℝ) (x0 : ℝ) (hx0 : x0 ∈ s)
    (hmeas : ∀ x ∈ s, AEStronglyMeasurable (F x) μ)
    (hbound : ∀ x ∈ s, ∀ᵐ y ∂μ, ‖F x y‖ ≤ bound y)
    (hbound_int : Integrable bound μ)
    (hcont : ∀ᵐ y ∂μ, ContinuousWithinAt (fun x => F x y) s x0) :
    ContinuousWithinAt (fun x => ∫ y, F x y ∂μ) s x0 := by sorry

end AvramDividend.Classical
