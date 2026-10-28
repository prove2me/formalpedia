-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_probability_of_poisson_count_no_jump_event
-- name    : AvramDividend.Classical.zero_probability_of_poisson_count_no_jump_event
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:56:22.087255+00:00
-- url     : https://prove2.me/theorems/aac9e95d-3e37-4c4a-952c-c53f64ab442a
-- title:
--   Poisson no-jump event is null when truncated jump intensities diverge
-- statement:
--   Suppose a measurable probability-space event A ensures zero occurrences for every one of a sequence of jump-count random variables. If each count has zero probability mass at zero equal to e^{-λ_n}, and the rates λ_n diverge, then A has probability zero. This directly combines the finite-intensity Poisson zero-count law with the established diverging-intensity bound and supplies the event-theoretic core of almost-sure early negative jumps.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1, zero barrier after (3.13), https://arxiv.org/pdf/math/0702893. Adapted mathematical structure from LeanLevy time-band count law, https://github.com/slink/LeanLevy.

import Theorems.Thm_AvramDividend_Classical_zero_probability_of_diverging_poisson_zero_count_bounds
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Basic

open AvramDividend.Classical MeasureTheory Set Filter
open scoped ENNReal

namespace AvramDividend.Classical

/-- Finite-band Poisson zero-count laws with divergent rates make a contained no-jump event null. -/
theorem zero_probability_of_poisson_count_no_jump_event
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (counts : ℕ → Ω → ℕ) (rates : ℕ → ℝ)
    (hrates : Tendsto rates atTop atTop)
    (hsubset : ∀ n : ℕ, A ⊆ {ω | counts n ω = 0})
    (hzeroLaw : ∀ n : ℕ,
      P {ω | counts n ω = 0} = ENNReal.ofReal (Real.exp (-(rates n)))) :
    P A = 0 := by sorry

end AvramDividend.Classical
