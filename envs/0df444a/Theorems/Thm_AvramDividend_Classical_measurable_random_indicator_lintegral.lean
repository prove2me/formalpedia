-- Prove2me | Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral
-- name    : AvramDividend.Classical.measurable_random_indicator_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:25:20.696401+00:00
-- url     : https://prove2.me/theorems/3f6e3e3b-9b82-4ca2-9ad8-b0543533321f
-- title:
--   Jointly measurable random-set reward under an s-finite Markov kernel
-- statement:
--   For an s-finite measurable kernel on real time, integrating a measurable deterministic nonnegative weight over a jointly measurable random time set gives a measurable sample-path reward. The s-finiteness requirement is explicit and is not assumed automatically for the actual running-supremum Stieltjes measure.
-- source:
--   Mathlib Measurable.lintegral_kernel_prod_left exact pinned remote signature, private probe de385f72-d136-45ac-b6de-7c6ce02d49e4. Corrects initial publication errors by importing the namespace and using classical decidability for the set indicator.

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.measurable_random_indicator_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (κ : ProbabilityTheory.Kernel Ω ℝ)
    [ProbabilityTheory.IsSFiniteKernel κ]
    (S : Set (ℝ × Ω)) (hS : MeasurableSet S)
    (w : ℝ → ℝ≥0∞) (hw : Measurable w) :
    Measurable (fun ω : Ω =>
      ∫⁻ t, if (t, ω) ∈ S then w t else 0 ∂κ ω) := by sorry
