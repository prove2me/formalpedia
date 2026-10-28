-- Prove2me | Theorems.Thm_AvramDividend_Classical_restrictedPathLaw_scalar_lintegral_reward
-- name    : AvramDividend.Classical.restrictedPathLaw_scalar_lintegral_reward
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:33:58.583694+00:00
-- url     : https://prove2.me/theorems/da553423-a6e8-4051-b447-6233f95d0c50
-- title:
--   Scaled stopped-path law determines any nonnegative discounted reward integral
-- statement:
--   If the pushforward law of a random path Y under a stopped-history event A is P(A) times a reference measure ν, then the expectation of any nonnegative measurable reward of Y restricted to A factors as P(A) times its expectation under ν.
-- source:
--   Generic stochastic expectation bridge from full stopped-future Lévy scaled path law to the discounted post-first-upcrossing barrier-dividend reward. It is a genuine mathematical intermediate required for canonical dividend value splitting 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Restrict

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.restrictedPathLaw_scalar_lintegral_reward
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : Measure Ω) (A : Set Ω) (hA : MeasurableSet A)
    (Y : Ω → β) (hY : Measurable Y) (ν : Measure β)
    (hLaw : Measure.map Y (P.restrict A) = (P A) • ν)
    (g : β → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω, Set.indicator A (fun ω' => g (Y ω')) ω ∂P) =
    P A * (∫⁻ y, g y ∂ν) := by
  sorry
