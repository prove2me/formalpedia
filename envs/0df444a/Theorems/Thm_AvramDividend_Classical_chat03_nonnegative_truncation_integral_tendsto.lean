-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_nonnegative_truncation_integral_tendsto
-- name    : AvramDividend.Classical.chat03_nonnegative_truncation_integral_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T09:48:03.20472+00:00
-- url     : https://prove2.me/theorems/1390c181-65ba-4b2a-85dd-2fff55ad8238
-- title:
--   Dominated convergence for nonnegative finite-threshold truncations
-- statement:
--   On a probability space, for an almost-everywhere convergent sequence of nonnegative strongly measurable real random variables, the expectations of the finite-threshold truncations min(Y_n,R) converge to the expectation of min(Z,R) for each fixed R≥0. The constant R dominates all truncated quantities, so dominated convergence applies without the uniform second-moment assumption.
-- source:
--   MeasureTheory.tendsto_integral_of_dominated_convergence, with the continuous truncation map y↦min(y,R), pointwise nonnegativity and the integrable constant R on a probability space.

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.OrderClosed

open MeasureTheory Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.chat03_nonnegative_truncation_integral_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hYm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hY0 : ∀ n, ∀ᵐ ω ∂P, 0 ≤ Y n ω)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Z ω))) :
    Tendsto (fun n => ∫ ω, min (Y n ω) R ∂P) atTop
      (𝓝 (∫ ω, min (Z ω) R ∂P)) := by sorry
