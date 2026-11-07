-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_zero_benchmark_signed_source_forces_payoff_zero
-- name    : AvramDividend.Classical.avram_p3_grid4_zero_benchmark_signed_source_forces_payoff_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:57:49.575678+00:00
-- url     : https://prove2.me/theorems/9d76492b-937e-44de-974f-e2afd8d33c8e
-- title:
--   At zero benchmark an integrable nonpositive-mean signed source forces any nonnegative dominated payoff to vanish almost surely
-- statement:
--   This closes the degenerate w(x)=0 branch after the existing Proved original residual witness f2a4acbb. When original strict cash plus terminal Y is nonnegative and dominated ae by an integrable source E of mean≤0, then E is ae nonnegative, its integral is zero and hence E=0 ae; Y=0 ae. This allows constant-zero genuine certificate witnesses in the zero-benchmark case. It does not assume the missing physical-source estimate.

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_zero_benchmark_signed_source_forces_payoff_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y E : Ω → ℝ)
    (hYpos : 0 ≤ᵐ[P] Y)
    (hEint : Integrable E P)
    (hEmean : (∫ ω, E ω ∂P) ≤ 0)
    (hYle : ∀ᵐ ω ∂P, Y ω ≤ E ω) :
    ∀ᵐ ω ∂P, Y ω = 0 := by sorry
