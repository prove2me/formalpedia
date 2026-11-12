-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite75_positive_part_integral_mono
-- name    : AvramDividend.Classical.avram_gfinite75_positive_part_integral_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T07:38:46.240647+00:00
-- url     : https://prove2.me/theorems/0be05981-12b0-4a4e-a6a5-5ac0c90fa515
-- title:
--   Almost-sure cash-residual domination bounds expected positive cash error
-- statement:
--   If two real random variables have integrable positive parts over a measurable event and one variable is almost surely bounded by the other on that event, then the expected positive part of the first is bounded by that of the second. This is the measure-theoretic bridge from a pathwise Gaussian cash ledger to an L1 error inequality.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.avram_gfinite75_positive_part_integral_mono
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (f g : Ω → ℝ)
    (hf : IntegrableOn (fun ω => max (f ω) 0) A P)
    (hg : IntegrableOn (fun ω => max (g ω) 0) A P)
    (hfg : ∀ᵐ ω ∂P.restrict A, f ω ≤ g ω) :
    (∫ ω in A, max (f ω) 0 ∂P) ≤
      (∫ ω in A, max (g ω) 0 ∂P) := by
  sorry
