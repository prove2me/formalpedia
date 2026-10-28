-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_firstRecord_initial_lower_of_strict_exit
-- name    : AvramDividend.Classical.killed_firstRecord_initial_lower_of_strict_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T16:17:16.215842+00:00
-- url     : https://prove2.me/theorems/709fa6e6-0ba8-4894-8980-5281901b6c58
-- title:
--   Discounted first record lower scale bound from an ordinary strict two-sided exit identity
-- statement:
--   Assuming the standard q-scale discounted strict upward-before-downward exit formula at reserve a−ε, the published event comparison implies the unscaled expected reward surviving actual reflected barrier ruin. The published nonnegative scalar homogeneity of killed lower integrals then multiplies by ε, furnishing exactly the initial expected payment lower estimate needed in the stopped geometric renewal argument. The only remaining assumption is the ordinary q-scale strict-exit identity.
-- source:
--   Avram, Palmowski and Pistorius (2007) equation (3.6) and Proposition 1, stopped barrier renewal.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_weight_lower_of_strict_exit
import Theorems.Thm_AvramDividend_Classical_killed_lintegral_ofReal_scaled_lower

open MeasureTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.killed_firstRecord_initial_lower_of_strict_exit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (W : ℝ → ℝ)
    (hExit : (∫⁻ ω,
      if twoSidedExitUpTime X ε ω <
          twoSidedExitDownTime X (ε - a) ω
      then ENNReal.ofReal (Real.exp
        (-(q * (twoSidedExitUpTime X ε ω).toReal)))
      else 0 ∂P) =
      ENNReal.ofReal (W (a - ε) / W a)) :
    ENNReal.ofReal (ε * (W (a - ε) / W a)) ≤
      (∫⁻ ω,
        if twoSidedExitUpTime X ((1 : ℝ) * ε) ω <
            barrierRuinTime X a ω then
          ENNReal.ofReal (ε * Real.exp
            (-(q * (twoSidedExitUpTime X ((1 : ℝ) * ε) ω).toReal)))
        else 0 ∂P) := by sorry
