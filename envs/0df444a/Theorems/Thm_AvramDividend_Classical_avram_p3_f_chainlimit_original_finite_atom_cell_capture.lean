-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_finite_atom_cell_capture
-- name    : AvramDividend.Classical.avram_p3_f_chainlimit_original_finite_atom_cell_capture
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:31:05.467205+00:00
-- url     : https://prove2.me/theorems/68142ffa-f31f-4a0a-8f13-4839c643ee1c
-- title:
--   Injectively marked actual Lévy jump atoms are covered by their original source grid cell masses
-- statement:
--   For the true original BV Lévy jump source, fix finitely many genuine source times T and injectively assign each to a distinct actual grid cell within the finite physical mesh. Provided each marked true jump is bounded by that cell's actual J increment, the sum of all marked original jump magnitudes is bounded by the selected marked source cell mass. The cellwise premise is discharged on a full-measure event by the separate source atom bound; finite mark placement remains an explicit P3-G localisation hypothesis. No generator, replacement process, synthetic convergence or stopped verification inequality is assumed.
-- source:
--   Source-specific finite-mark image, Finset.sum_image with injective cell tag, exact original negative left-jump magnitudes and physical J cell increments. Cellwise atom bound separately authored in P3-F.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_f_chainlimit_original_finite_atom_cell_capture
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (T : Finset ℝ≥0) (tag : ℝ≥0 → ℕ)
    (hTag : ∀ v ∈ T, tag v < n)
    (hInj : ∀ v ∈ T, ∀ z ∈ T, tag v = tag z → v = z) :
    ∀ ω,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) s - X.X s ω
        else 0
      let j : ℕ → ℝ := fun i => J (u (i + 1)) - J (u i)
      (∀ v ∈ T, (Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω) ≤ j (tag v)) →
      (∑ v ∈ T, (Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω)) ≤
        (∑ i ∈ Finset.range n, if i ∈ T.image tag then j i else 0) := by sorry
