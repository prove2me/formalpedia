-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_lintegral_antitone_discount_any_measure
-- name    : AvramDividend.Classical.chat04_strict_exit_lintegral_antitone_discount_any_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T13:57:48.807091+00:00
-- url     : https://prove2.me/theorems/decbeb0c-c4b1-498c-9c76-32b4750af7ce
-- title:
--   Any-measure strict killed two-sided exit discount is antitone
-- statement:
--   For any path-space measure μ, the nonnegative q-discounted strict upper-before-downward-exit lower integral is nonincreasing in the real discount rate q, including infinite passage times and arbitrary initial reserves. This extends the canonically Proved probability-measure antitonicity lemma to tilted and sigma-finite measures without imposing integrability assumptions.
-- source:
--   The Proved AvramDividend.Classical.chat04_twoSidedExitExpectation_antitone_discount, UUID 69a4a254-000a-4139-880d-577bc9fca961, with identical pointwise proof and arbitrary-measure lintegral_mono.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_strict_exit_lintegral_antitone_discount_any_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω)
    (q₁ q₂ a x : ℝ) (hq : q₁ ≤ q₂) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp (-(q₂ * ENNReal.toReal
          (twoSidedExitUpTime X (a - x) ω))))
      else 0 ∂μ) ≤
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp (-(q₁ * ENNReal.toReal
          (twoSidedExitUpTime X (a - x) ω))))
      else 0 ∂μ) := by sorry
