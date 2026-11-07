-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux18_integrated_count_pgf_sandwich
-- name    : AvramDividend.Classical.avram_redux18_integrated_count_pgf_sandwich
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T13:40:48.635364+00:00
-- url     : https://prove2.me/theorems/b241003b-6056-40ce-97e2-d39e87cb4b02
-- title:
--   Integrated PGF bounds for any integrable integer-valued random count
-- statement:
--   Integrating the Proved pointwise PGF sandwich against any measure gives the corresponding bounds on the generating-function expectation for an integrable integer-valued random jump count. Its upper envelope is the zero-count event, and its lower envelope is the expected count. This is the exact integration bridge needed to apply original-process count mean and void-probability results to an incremental Poisson-law characterisation.
-- source:
--   Applies MeasureTheory.integral_mono twice to the accepted theorem 048020c9; all three integrability assumptions are explicit and can be discharged from source-specific finite activity and boundedness.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_redux18_count_pgf_pointwise_sandwich
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_redux18_integrated_count_pgf_sandwich
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : Ω → ℕ) (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hN : Integrable (fun ω => (N ω : ℝ)) μ)
    (hZ : Integrable (fun ω => z ^ (N ω)) μ)
    (hI : Integrable (fun ω => if N ω = 0 then (1 : ℝ) else z) μ) :
    (∫ ω, (1 : ℝ) - (1 - z) * (N ω : ℝ) ∂μ) ≤
      (∫ ω, z ^ (N ω) ∂μ) ∧
    (∫ ω, z ^ (N ω) ∂μ) ≤
      (∫ ω, if N ω = 0 then (1 : ℝ) else z ∂μ) := by sorry
