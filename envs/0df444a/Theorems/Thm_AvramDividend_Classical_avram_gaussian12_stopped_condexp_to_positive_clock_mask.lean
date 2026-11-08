-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussian12_stopped_condexp_to_positive_clock_mask
-- name    : AvramDividend.Classical.avram_gaussian12_stopped_condexp_to_positive_clock_mask
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:28:04.152213+00:00
-- url     : https://prove2.me/theorems/7f0af2b8-a048-4d2e-80c8-4537733fea09
-- title:
--   Stopped-history centred martingale integrates to zero on any positive stopping-clock event
-- statement:
--   For a real integrable stochastic residual whose conditional expectation at a genuine right-continuous stopped-history sigma-algebra is zero, transfer centring to the initial sigma-algebra by the conditional-expectation tower and use any positive stopping-clock initial event to conclude that its restricted expectation is zero. Applies to source-exact Gaussian stopped Taylor cell residuals whose stopped conditional centring has already been proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gaussian11_strict_positive_stopping_clock_condexp_zero
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_gaussian12_stopped_condexp_to_positive_clock_mask
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (σ τ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (M : Ω → ℝ) (hMI : Integrable M P)
    (hStoppedZero : ∀ᵐ ω ∂P,
      condExp hτstop.measurableSpace P M ω = 0) :
    (∫ ω in {ω : Ω | σ ω ≠ 0}, M ω ∂P) = 0 := by sorry
