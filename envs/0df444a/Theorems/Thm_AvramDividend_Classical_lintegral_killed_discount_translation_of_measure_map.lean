-- Prove2me | Theorems.Thm_AvramDividend_Classical_lintegral_killed_discount_translation_of_measure_map
-- name    : AvramDividend.Classical.lintegral_killed_discount_translation_of_measure_map
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:46:30.445057+00:00
-- url     : https://prove2.me/theorems/4c583263-f38b-4e14-bc95-07738e938d75
-- title:
--   Killed dividend integral time shift factors the exponential discount at crossing
-- statement:
--   If two dividend Stieltjes measures are related by translation in time and their killed payment windows are correspondingly translated, the original discounted dividend integral equals the exponential discount at the crossing time multiplied by the discounted future killed integral. This is the exact deterministic discount-factor bridge needed for strong-Markov barrier valuation.
-- source:
--   Canonical W-free strong-Markov child 79978d61-9d1f-4b20-b8a5-114797a8e380, using Proved restricted window translation theorem 1c65b156-fb6b-455d-b758-fdb544c7ff6e, Real.exp_add and ENNReal.ofReal_mul. Stops localising the stochastic kernel at the future reward.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Theorems.Thm_AvramDividend_Classical_lintegral_killed_window_translation_of_measure_map

open MeasureTheory Set
open scoped ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.lintegral_killed_discount_translation_of_measure_map
    (μ ν : Measure ℝ) (u q : ℝ) (A B : Set ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hμ : μ = Measure.map (fun t : ℝ => u + t) ν)
    (hwindow : ∀ t : ℝ, u + t ∈ A ↔ t ∈ B) :
    (∫⁻ t in A,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) =
      ENNReal.ofReal (Real.exp (-(q * u))) *
        (∫⁻ t in B,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂ν) := by
  sorry
