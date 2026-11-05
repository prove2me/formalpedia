-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_finite_source_tagged_capture
-- name    : AvramDividend.Classical.avram_p3_f_chainlimit_original_finite_source_tagged_capture
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:52:13.424374+00:00
-- url     : https://prove2.me/theorems/11e630d3-2930-4d7e-bc68-38a4925e470b
-- title:
--   Actual original BV finite negative jump marks have injective right-closed cell tags and exact J-mass domination
-- statement:
--   For the genuine original spectrally negative BV Lévy source X and a finite set of physical jump times T, assume each mark is covered by a right-closed grid cell and distinct marks are separated by cells. Then almost surely there is an injective physical cell assignment whose source negative-jump atom mass is bounded by the actual J increment in its physical cell. Finset.sum expressions are explicit to avoid scoped variable resolution ambiguities in authoring.
-- source:
--   Proved physical F9 positive atom ≤ actual J cell b59097be and F10 finite atom capture 68142ffa; classical choice of physical cell cover.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_positive_atom_le_actual_J_cell
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_finite_atom_cell_capture
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_f_chainlimit_original_finite_source_tagged_capture
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
        T.sum (fun v =>
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω) ≤
          (Finset.range n).sum (fun i =>
            if i ∈ T.image tag then
              J (u (i + 1)) - J (u i) else 0) := by sorry
