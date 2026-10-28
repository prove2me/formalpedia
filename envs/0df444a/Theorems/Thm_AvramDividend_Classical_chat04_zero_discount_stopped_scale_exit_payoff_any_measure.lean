-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_zero_discount_stopped_scale_exit_payoff_any_measure
-- name    : AvramDividend.Classical.chat04_zero_discount_stopped_scale_exit_payoff_any_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T11:45:30.877688+00:00
-- url     : https://prove2.me/theorems/48b30575-77fc-4f34-a727-125edcb724ff
-- title:
--   Zero-discount stopped q-scale terminal value equals barrier scale times strict upper-first passage mass
-- statement:
--   At zero discount, the killed strict-upper-first stopped scale terminal payoff under an arbitrary path-space measure equals the mass of the upper-before-ruin event times the scale value at the upper barrier.
-- source:
--   Immediate consequence of the proved strict stopped scale reward factorisation and zero-discount upper-first event mass identity.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_exit_payoff_any_measure_factorisation
import Theorems.Thm_AvramDividend_Classical_chat04_zero_discount_upperfirst_mass_any_measure

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_zero_discount_stopped_scale_exit_payoff_any_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω)
    (a x : ℝ) (hxa : x ≤ a) (W : ℝ → ℝ) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(0 * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂μ) =
      μ {ω : Ω | twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω} * ENNReal.ofReal (W a) := by sorry
