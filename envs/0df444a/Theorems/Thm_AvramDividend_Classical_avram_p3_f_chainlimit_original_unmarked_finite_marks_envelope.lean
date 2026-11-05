-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_unmarked_finite_marks_envelope
-- name    : AvramDividend.Classical.avram_p3_f_chainlimit_original_unmarked_finite_marks_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T15:02:05.996317+00:00
-- url     : https://prove2.me/theorems/d24cecb4-6b7d-49cf-87c5-b7a595aa29fe
-- title:
--   Actual original BV unmarked jump-cell mass dominated by excluded physical finite-mark complement
-- statement:
--   Source-exact physical finite jump-cell separation yields a direct bound of the original unmarked J mass by the source J interval total less the selected finite original jump atoms. Requires F22 accepted tagged physical capture and F16 accepted uniform unmarked jump exclusion.
-- source:
--   F22 original finite source tag capture and F16 uniform ae original unmarked jump finite exclusion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_finite_source_tagged_capture
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_uniform_ae_unmarked_J_finite_exclusion
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_f_chainlimit_original_unmarked_finite_marks_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (u : ℕ → ℝ≥0) (n : ℕ) (T : Finset ℝ≥0)
    (hCover : ∀ v ∈ T, ∃ i : ℕ,
      i < n ∧ u i < v ∧ v ≤ u (i + 1))
    (hSeparate : ∀ v ∈ T, ∀ z ∈ T, ∀ i : ℕ,
      i < n → u i < v → v ≤ u (i + 1) →
      u i < z → z ≤ u (i + 1) → v = z) :
    ∀ᵐ ω ∂P,
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
