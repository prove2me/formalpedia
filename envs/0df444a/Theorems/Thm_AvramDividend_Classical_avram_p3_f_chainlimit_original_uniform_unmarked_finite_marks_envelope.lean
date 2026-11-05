-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_uniform_unmarked_finite_marks_envelope
-- name    : AvramDividend.Classical.avram_p3_f_chainlimit_original_uniform_unmarked_finite_marks_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T15:17:17.741749+00:00
-- url     : https://prove2.me/theorems/41c6650f-44aa-4a84-9d5b-6da3a2cc637c
-- title:
--   Uniform almost-sure original BV unmarked negative-jump mass under path-dependent finite marks
-- statement:
--   On one original-source full-measure event and for every physical grid and finite negative jump time set chosen after fixing the sample, the unmarked original J-cell total is bounded by the actual interval J-mass less the finite selected original jump atoms. Imports the uniform finite marking helper and accepted original uniform unmarked exclusion.
-- source:
--   F22 original finite source tag capture and F16 uniform ae original unmarked jump finite exclusion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_uniform_finite_source_tagged_capture
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_uniform_ae_unmarked_J_finite_exclusion
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_f_chainlimit_original_uniform_unmarked_finite_marks_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      ∀ (u : ℕ → ℝ≥0) (n : ℕ) (T : Finset ℝ≥0)
        (hCover : ∀ v ∈ T, ∃ i : ℕ,
          i < n ∧ u i < v ∧ v ≤ u (i + 1))
        (hSeparate : ∀ v ∈ T, ∀ z ∈ T, ∀ i : ℕ,
          i < n → u i < v → v ≤ u (i + 1) →
          u i < z → z ≤ u (i + 1) → v = z),
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) s - X.X s ω
        else 0
      ∃ tag : ℝ≥0 → ℕ,
        (∀ v ∈ T,
          tag v < n ∧ u (tag v) < v ∧ v ≤ u (tag v + 1)) ∧
        (∀ v ∈ T, ∀ z ∈ T, tag v = tag z → v = z) ∧
        (Finset.range n).sum (fun i =>
          if i ∈ T.image tag then 0
          else J (u (i + 1)) - J (u i)) ≤
        J (u n) - J (u 0) -
          T.sum (fun v =>
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω) := by sorry
