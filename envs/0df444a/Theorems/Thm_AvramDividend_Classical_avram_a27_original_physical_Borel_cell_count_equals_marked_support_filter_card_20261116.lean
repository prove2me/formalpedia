-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_Borel_cell_count_equals_marked_support_filter_card_20261116
-- name    : AvramDividend.Classical.avram_a27_original_physical_Borel_cell_count_equals_marked_support_filter_card_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T09:12:28.922336+00:00
-- url     : https://prove2.me/theorems/11e24cb0-d1c2-40e2-b46c-5061867a4f2d
-- title:
--   Original physical negative-Borel cell count equals cardinality of its filtered finite marked-time support
-- statement:
--   For the original spectrally negative Lévy path and an exact finite marked-jump support S on (0,T], the true original physical B-marked jump count in any subinterval (s,t] equals the cardinal of S filtered to that interval. This follows directly from the Proved original intrinsic window count-cardinality theorem 8f1dd77e, with a finite-set equality derived from the support membership equivalence. Retains original Ω, P and filtration.
-- source:
--   Proved original Borel physical finite marked-window count cardinal 8f1dd77e, finite set filtering.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a27_original_physical_Borel_cell_count_equals_marked_support_filter_card_20261116
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (S : Finset ℝ≥0)
    (hS : ∀ u : ℝ≥0, u ∈ S ↔
       0 < u ∧ u ≤ T ∧
       X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
       X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B)
    (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) :
    ((Measure.count.restrict {u : ℝ≥0 |
       0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc s t ×ˢ B) =
       (((S.filter (fun u : ℝ≥0 => s < u ∧ u ≤ t)).card : ℕ) : ℝ≥0∞) := by sorry
