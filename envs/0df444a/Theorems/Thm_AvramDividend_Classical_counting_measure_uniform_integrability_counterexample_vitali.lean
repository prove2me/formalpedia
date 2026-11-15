-- Prove2me | Theorems.Thm_AvramDividend_Classical_counting_measure_uniform_integrability_counterexample_vitali
-- name    : AvramDividend.Classical.counting_measure_uniform_integrability_counterexample_vitali
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:32:13.648295+00:00
-- url     : https://prove2.me/theorems/24ee7e68-0716-4e03-933b-12c56d3f9766
-- title:
--   Infinite counting-measure uniformly integrable sequence with divergent Vitali means
-- statement:
--   A concrete uniformly integrable family on infinite counting measure converges pointwise to zero but every member has expectation one. Take the singleton indicator at n. Each member has L1 norm one, the family is uniformly absolutely continuous under counting measure, and the mass escapes to infinity. This formal counterexample explains why the unrestricted arbitrary-measure Vitali and bounded L2/L1 mean-convergence statements require finite mass or an additional tightness hypothesis.
-- source:
--   Counterexample certificate for retired Avram arbitrary-measure Vitali candidate a1ad8b30 and Open 685bb004. The correct finite-measure Vitali theorem b1b85a32 is Proved.

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.counting_measure_uniform_integrability_counterexample_vitali :
    ∃ Y : ℕ → ℕ → ℝ,
      UniformIntegrable Y 1 (Measure.count : Measure ℕ) ∧
      (∀ ω : ℕ, Tendsto (fun n => Y n ω) atTop (nhds 0)) ∧
      (∀ n : ℕ, (∫ ω, Y n ω ∂(Measure.count : Measure ℕ)) = 1) := by sorry
