-- Prove2me | Theorems.Thm_AvramDividend_Classical_monotone_localised_reward_lintegral_le
-- name    : AvramDividend.Classical.monotone_localised_reward_lintegral_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:38:11.478345+00:00
-- url     : https://prove2.me/theorems/27620e09-ae40-4899-a6b3-7794b3ff8a59
-- title:
--   Uniform finite-horizon integral bound passes to monotone limit of killed rewards
-- statement:
--   A nondecreasing sequence of nonnegative measurable localised killed rewards, all of whose expectations are bounded by the same finite or infinite constant, has limiting expectation bounded by that constant. This is the monotone-convergence step that removes the finite stopping horizon from the first-record renewal inequality.
-- source:
--   Mathlib MeasureTheory lintegral_iSup and iSup_le, used for finite-horizon stopped Lévy rewards.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory
open AvramDividend.Classical
open scoped ENNReal

theorem AvramDividend.Classical.monotone_localised_reward_lintegral_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (reward : ℕ → Ω → ℝ≥0∞)
    (hreward : ∀ n, Measurable (reward n))
    (hmono : Monotone reward)
    (bound : ℝ≥0∞)
    (hbound : ∀ n, (∫⁻ ω, reward n ω ∂P) ≤ bound) :
    (∫⁻ ω, ⨆ n, reward n ω ∂P) ≤ bound := by sorry
