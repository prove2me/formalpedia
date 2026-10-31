-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_stronglyPredictable_inclusive_horizon
-- name    : AvramDividend.Classical.avram_wave3_04_stronglyPredictable_inclusive_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T13:10:33.829175+00:00
-- url     : https://prove2.me/theorems/693b22ed-0842-4e61-add7-7439cb0f2f12
-- title:
--   Finite deterministic inclusive-horizon truncation preserves strong predictability
-- statement:
--   For a strongly predictable real-valued process Z and a deterministic nonnegative horizon T, the process Z_t 1_{t≤T}, including its terminal value at T, is strongly predictable for the identical filtration. The proof constructs the predictable set [0,T]×Ω as the complement of the predictable set (T,∞)×Ω, then applies the measurable if-then-else closure. This supports finite-horizon localisation of the genuine controlled-dividend stochastic integrand.
-- source:
--   Pinned Mathlib measurableSet_predictable_Ioi_prod, measurable if-then-else and strong measurability for real-valued functions. Private exact compiler probe a8799ff6-6a35-4ae0-9bd9-68428f35390c reached sentinel with no candidate errors, source SHA-256 7de8ef6270daac819abeb5ade26ea78a133d16771a047374eaa360eabc94944d.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_wave3_04_stronglyPredictable_inclusive_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Z : ℝ≥0 → Ω → ℝ)
    (hZ : IsStronglyPredictable 𝓕 Z)
    (T : ℝ≥0) :
    IsStronglyPredictable 𝓕
      (fun t ω => if t ≤ T then Z t ω else 0) := by sorry
