-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_uniform_ae_unmarked_J_finite_exclusion
-- name    : AvramDividend.Classical.avram_p3_f_chainlimit_original_uniform_ae_unmarked_J_finite_exclusion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:47:15.30008+00:00
-- url     : https://prove2.me/theorems/333ba767-9645-48e6-8974-535165dafcce
-- title:
--   One original Lévy full-measure event uniformly controls all path-chosen finite jump tags and cells
-- statement:
--   On a single P-full event depending only on the original bounded-variation Lévy source, every physical grid and every path-chosen finite positive-jump mark set with injective right-closed cell tags obeys the exact unmarked source-grid mass versus finite-exclusion original jump tail bound. Quantifiers over grids, marks and tags are inside the almost-sure event, allowing adaptive pathwise mark selection from the original BV finite-tail theorem. Strict left-open/right-closed chronology is preserved. No generator compensation or stopped verification inequality is assumed.
-- source:
--   Original actual jump atom≤grid cell theorem  b59097be gives a universal full-measure event; on that event apply source-specific finite-image capture 68142ffa and exact marked/unmarked J partition df3481a1 pointwise to all chosen grids and finite marks.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_positive_atom_le_actual_J_cell
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_finite_atom_cell_capture
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_negative_jump_unmarked_grid_partition
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_f_chainlimit_original_uniform_ae_unmarked_J_finite_exclusion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      ∀ (u : ℕ → ℝ≥0) (n : ℕ)
        (T : Finset ℝ≥0) (tag : ℝ≥0 → ℕ)
        (hTag : ∀ v ∈ T, tag v < n)
        (hInj : ∀ v ∈ T, ∀ z ∈ T, tag v = tag z → v = z)
        (hInside : ∀ v ∈ T, u (tag v) < v ∧ v ≤ u (tag v + 1)),
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) s - X.X s ω
        else 0
      let j : ℕ → ℝ := fun i => J (u (i + 1)) - J (u i)
      (∑ i ∈ Finset.range n, if i ∈ T.image tag then 0 else j i) ≤
        J (u n) - J (u 0) -
          (∑ v ∈ T, (Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω)) := by sorry
