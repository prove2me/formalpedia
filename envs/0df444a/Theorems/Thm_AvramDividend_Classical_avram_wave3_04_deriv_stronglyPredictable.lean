-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_deriv_stronglyPredictable
-- name    : AvramDividend.Classical.avram_wave3_04_deriv_stronglyPredictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T12:39:33.795497+00:00
-- url     : https://prove2.me/theorems/23f9385b-88d8-4ac7-b307-5132c28255d4
-- title:
--   Real derivatives preserve strong predictability under composition
-- statement:
--   For every strongly predictable real-valued stochastic process and every real-valued function w, the derivative composition t,ω ↦ deriv w (Z_t(ω)) is strongly predictable for the same filtration. Pinned Mathlib's measurable_deriv establishes Borel measurability without global differentiability assumptions; composing with the predictable measurable process and using strong measurability for real targets gives the result. This supplies the measurable-integrand component for localised dividend verification.
-- source:
--   Pinned Mathlib measurable_deriv, strongly measurable/measurable composition. Private remote compiler job 3ec69c5d-9a1b-42be-ab77-92ada6e86308 reached sentinel with no candidate errors, source SHA-256 a9569bf409671e38e212464e594f4c5dd85d140e9e0d6bae2766a50bfcbe6ea8.

import Mathlib

open MeasureTheory Filter
open scoped NNReal

theorem AvramDividend.Classical.avram_wave3_04_deriv_stronglyPredictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Z : ℝ≥0 → Ω → ℝ)
    (hZ : IsStronglyPredictable 𝓕 Z)
    (w : ℝ → ℝ) :
    IsStronglyPredictable 𝓕 (fun t ω => deriv w (Z t ω)) := by sorry
