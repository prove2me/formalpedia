-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_predictable_rational_level
-- name    : AvramDividend.Classical.avram_wave3_04_predictable_rational_level
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T23:29:22.954552+00:00
-- url     : https://prove2.me/theorems/f9e7bb32-52ee-4d98-8a72-b1150ddc7ed4
-- title:
--   Monotone adapted dividend processes with rational left-approximation are predictable
-- statement:
--   An adapted, pathwise nondecreasing real process starting at zero is measurable for the original predictable sigma algebra whenever each strict upper level at a positive time is already attained at some earlier nonnegative rational time. This set-level criterion reduces source dividend-strategy predictability to the genuine left-continuity and rational density argument.
-- source:
--   Mathlib Probability.Process.Predictable's Ioi product generators, measurable_of_Ioi, and the original filtration. Exact full source passed private pinned remote compiler through the intentional sentinel, candidate SHA-256 8d43d226d9a0d96b1307f589cdba96cbb1fe59455628f4efa0f5170a2ba35411, job 10de1eff-8af9-4b14-ad85-b847a241b236. Supports Avram Palmowski Pistorius (2007), Proposition 4(i).

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_predictable_rational_level
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (D : ℝ≥0 → Ω → ℝ)
    (hzero : ∀ ω, D 0 ω = 0)
    (hadapt : Adapted 𝓕 D)
    (hmono : ∀ ω, Monotone (fun t => D t ω))
    (hdense : ∀ ω t (a : ℝ), t ≠ 0 → a < D t ω →
      ∃ r : ℚ≥0, (r : ℝ≥0) < t ∧ a < D (r : ℝ≥0) ω) :
    @Measurable (ℝ≥0 × Ω) ℝ 𝓕.predictable inferInstance
      (fun p => D p.1 p.2) := by sorry
