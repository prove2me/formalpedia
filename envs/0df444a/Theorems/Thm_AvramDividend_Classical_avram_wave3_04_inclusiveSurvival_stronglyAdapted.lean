-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyAdapted
-- name    : AvramDividend.Classical.avram_wave3_04_inclusiveSurvival_stronglyAdapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T13:15:58.892994+00:00
-- url     : https://prove2.me/theorems/77be6df8-9531-4e71-97a3-d24e86fc3da3
-- title:
--   Inclusive survival indicator of any stopping time is strongly adapted
-- statement:
--   For any extended-nonnegative-valued stopping time and filtration, the inclusive survival indicator t,ω↦1_{t≤τ(ω)} is strongly adapted. Mathlib IsStoppingTime.measurableSet_ge provides the survival event in F_t; the real-valued if-then-else is therefore strongly measurable for each t. The theorem requires no Lévy assumptions.
-- source:
--   Pinned Mathlib IsStoppingTime.measurableSet_ge. Private remote compiler probe 23c8bc09-827f-4d1d-893a-a1e57f65d966 passed its sentinel with no candidate errors; source SHA-256 304d82f1d68dbed8a351a597a8bf3a535c6c24606a020b6a49a62c3fad4260b6.

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_inclusiveSurvival_stronglyAdapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0∞)
    (hτ : IsStoppingTime 𝓕 τ) :
    StronglyAdapted 𝓕
      (fun t ω => if (t : ℝ≥0∞) ≤ τ ω then (1 : ℝ) else 0) := by sorry
