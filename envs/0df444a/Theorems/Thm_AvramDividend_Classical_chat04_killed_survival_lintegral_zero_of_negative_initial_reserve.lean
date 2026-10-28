-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_survival_lintegral_zero_of_negative_initial_reserve
-- name    : AvramDividend.Classical.chat04_killed_survival_lintegral_zero_of_negative_initial_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T07:17:07.781445+00:00
-- url     : https://prove2.me/theorems/82a74188-f140-406b-94e4-b3e3605e61b2
-- title:
--   Killing at time zero makes the discounted scale expectation vanish from negative capital
-- statement:
--   For negative initial reserve, survival through any nonnegative horizon is impossible because the initial reserve at time zero is already below zero. The corresponding killed discounted q-scale integral vanishes. The scale function also vanishes at negative arguments, hence the renewal identity holds unconditionally in the negative-capital case.
-- source:
--   Direct negative-reserve branch of the Open AvramDividend.Classical.chat04_unbounded_killed_survival_discounted_scale_expectation (a885f0b3-3960-424d-97e4-abbcffe268ba), which is the needed killed-scale harmonicity prerequisite of chat04_unbounded_two_sided_exit_stopped_scale_identity (aed50a34-200b-4736-a369-5ae8473e3258). Uses only SpectrallyNegativeLevy.X_zero and the negative-support clause of IsScaleFunction.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_killed_survival_lintegral_zero_of_negative_initial_reserve
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : x < 0) (t : ℝ≥0) :
    (∫⁻ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω))) ω ∂P) =
      ENNReal.ofReal (W x) := by sorry
