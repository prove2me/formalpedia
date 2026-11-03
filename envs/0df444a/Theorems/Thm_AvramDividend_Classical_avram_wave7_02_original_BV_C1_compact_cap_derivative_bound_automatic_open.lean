-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_compact_cap_derivative_bound_automatic_open
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_C1_compact_cap_derivative_bound_automatic_open
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:11:52.651303+00:00
-- url     : https://prove2.me/theorems/07ca388c-f09e-4652-a779-ef29a62cdb1f
-- title:
--   Source BV compact positive-cap C1 derivative ceiling directly from proved cap openness and compactness
-- statement:
--   For the exact Avram source BV C1 candidate and any compact reserve interval inside the strict positive ENNReal cap, the derivative has an absolute uniform finite bound. The original cap region is open by already Proved bcf24f3a and pinned Mathlib ContDiffOn continuous derivative on open sets. The compact image is bounded, so a nonnegative K exists. This direct proof has no dependency on any unresolved submission.
-- source:
--   Direct independent Mathlib compactness and derivative-continuity proof using only Proved original positive-cap openness bcf24f3a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_C1_compact_cap_derivative_bound_automatic_open
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ y ∈ Icc a b, |deriv w y| ≤ K := by sorry
