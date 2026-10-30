-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_03_min_stopped_qscale_reward_measurable
-- name    : AvramDividend.Classical.avram_root29_03_min_stopped_qscale_reward_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:01:13.646345+00:00
-- url     : https://prove2.me/theorems/d1115052-bd26-4f76-9602-475d85054c6e
-- title:
--   Genuine original Lévy q-scale discounted terminal payoff at minimum exit clock is measurable
-- statement:
--   The actual original spectrally negative Lévy process and source-defined strict upper and lower first passage clocks have a measurable discounted q-scale terminal reward evaluated at the minimum exit clock, even when that clock is infinite and toNNReal is used. Requires only IsScaleFunction X q W; no Standing, BV, UBV, q>0, no-creeping or killed harmonicity assumption. This discharges the exact measurability binder needed to instantiate the independently Proved finite-stopped-minimum two-branch payoff conversion with the genuine discounted source q-scale reward.
-- source:
--   Imports canonically Proved measurability of both true passage clocks 3d4daa72, joint Lévy time/path evaluation d55462c3, and arbitrary q-scale Borel measurability 344f3813. Pure measurable composition, no stochastic optional stopping.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_both_named_passage_clocks_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_03_min_stopped_qscale_reward_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) :
    Measurable (fun ω : Ω =>
      ENNReal.ofReal
        (Real.exp (-(q * ENNReal.toReal (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω))))) *
      ENNReal.ofReal (W (x + X.X (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω)).toNNReal ω))) := by sorry
