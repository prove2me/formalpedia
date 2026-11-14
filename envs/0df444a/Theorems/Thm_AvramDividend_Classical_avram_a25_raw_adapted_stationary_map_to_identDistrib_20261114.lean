-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_raw_adapted_stationary_map_to_identDistrib_20261114
-- name    : AvramDividend.Classical.avram_a25_raw_adapted_stationary_map_to_identDistrib_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:20:34.676186+00:00
-- url     : https://prove2.me/theorems/3edd2e46-b1a8-4076-99b4-a2d20ca553da
-- title:
--   Raw-filtration adapted stationary pushforward increments imply exact IdentDistrib Levy structure field
-- statement:
--   Any original raw-filtration adapted real process with stationary pushforward increment laws satisfies exactly the IdentDistrib stationary increment requirement of the spectrally negative Levy process structure.
-- source:
--   Mathlib IdentDistrib, adaptation, Measure.map and add_tsub_cancel_of_le.

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

/-- Adaptation and stationary pushforward laws imply the exact IdentDistrib field of a Levy process. -/

theorem AvramDividend.Classical.avram_a25_raw_adapted_stationary_map_to_identDistrib_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (G : ℝ≥0 → Ω → ℝ)
    (hAdapt : ∀ t : ℝ≥0, Measurable[𝓕 t] (G t))
    (hLaw : ∀ s T : ℝ≥0,
      Measure.map (fun ω => G (s + T) ω - G s ω) P =
        Measure.map (G T) P) :
    ∀ s t : ℝ≥0, s ≤ t →
      IdentDistrib (fun ω => G t ω - G s ω) (G (t - s)) P P := by sorry
