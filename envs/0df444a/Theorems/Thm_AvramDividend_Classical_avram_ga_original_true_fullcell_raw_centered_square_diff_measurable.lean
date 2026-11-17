-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_original_true_fullcell_raw_centered_square_diff_measurable
-- name    : AvramDividend.Classical.avram_ga_original_true_fullcell_raw_centered_square_diff_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T18:57:51.410191+00:00
-- url     : https://prove2.me/theorems/ab682771-86fa-4828-ab43-7cdc56da76ea
-- title:
--   Original stopped Gaussian full-cell raw-centred squared difference is measurable
-- statement:
--   For every deterministic physical-grid cell, the original Lévy process raw increment squared minus its drift-centred squared increment, multiplied by the true fullcell stop mask s<rho and s+Δ≤rho, is measurable. Derive from adaptedness of X at deterministic times and measurability of the stopping clock.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_ga_original_true_fullcell_raw_centered_square_diff_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0))) :
    ∀ m i : ℕ, Measurable (fun ω : Ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      let R : ℝ := X.X (s + Δ) ω - X.X s ω
      let Z : ℝ := R - (Δ : ℝ) * X.c
      if s < ρ ω ∧ s + Δ ≤ ρ ω then R ^ 2 - Z ^ 2 else 0)
    := by sorry
