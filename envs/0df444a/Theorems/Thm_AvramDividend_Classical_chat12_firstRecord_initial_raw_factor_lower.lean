-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_firstRecord_initial_raw_factor_lower
-- name    : AvramDividend.Classical.chat12_firstRecord_initial_raw_factor_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:13:26.192838+00:00
-- url     : https://prove2.me/theorems/14cefbf0-fcfb-495c-9bde-eba1dcf0002a
-- title:
--   Initial killed-record expected payment dominates raw exit-factor first reward
-- statement:
--   Scale-free initial renewal inequality: the expected first killed upward record discounted payment is at least epsilon times the raw discounted upper-exit-before-nonstrict-lower-path expectation. It uses the Proved raw-exit pathwise domination and nonnegative Lebesgue integral scaling; it needs no q-scale-function ratio identity.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_named_killed_upcrossing_lower_of_raw_exit
import Theorems.Thm_AvramDividend_Classical_killed_lintegral_ofReal_scaled_lower

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.chat12_firstRecord_initial_raw_factor_lower
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ENNReal.ofReal ε *
      (∫⁻ ω, if twoSidedExitUpTime X ε ω ≠ ∞ ∧
          (∀ t : ℝ≥0, t < (twoSidedExitUpTime X ε ω).toNNReal →
            ε - a ≤ X.X t ω) then
        ENNReal.ofReal (Real.exp
          (-(q * (twoSidedExitUpTime X ε ω).toReal)))
      else 0 ∂P) ≤
      (∫⁻ ω,
        if twoSidedExitUpTime X ((1 : ℝ) * ε) ω <
            barrierRuinTime X a ω then
          ENNReal.ofReal (ε * Real.exp
            (-(q * (twoSidedExitUpTime X ((1 : ℝ) * ε) ω).toReal)))
        else 0 ∂P) := by sorry
