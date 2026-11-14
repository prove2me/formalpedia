-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b171_original_canonical_true_marked_grid_card_le_original_poisson
-- name    : AvramDividend.Classical.avram_b171_original_canonical_true_marked_grid_card_le_original_poisson
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:12:44.185457+00:00
-- url     : https://prove2.me/theorems/893a1b02-a7b2-4c4e-bc7c-38edaade1fe3
-- title:
--   Canonical genuine original negative-jump containing finite monotone random-grid cells are pathwise dominated by complete original negative Poisson count
-- statement:
--   For the exact original spectrally negative Lévy process, consider an arbitrary finite family of monotone potentially random physical clock grid intervals ending before a fixed bounded horizon. Define the canonical genuinely marked Finset by selecting precisely those cells containing an actual nonzero original source jump in the half-open physical clock interval. Its ENNReal cardinal is bounded on every path, including exceptional infinite-activity paths, by the original mapped full negative-jump Poisson source count up to the horizon. The prepared B163 establishes source count domination for any finitely selected genuinely marked monotone cells. The canonical Finset filter provides its own actual source jump witness for each selected cell, while the grid range hypothesis bounds its source times. This directly discharges the physical negative jump contact source domination premise in the Proved B150 and pending B157 original mixed Gaussian/negative jump finite-mesh energy estimates for canonical physically marked grid selection. Publication waits for B163 Proved.
-- source:
--   Prepared B163 full original source monotone grid marked-cell cardinal domination, canonical original Finset.filter physical jump classification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b163_original_true_marked_monotone_grid_card_le_full_negative_poisson
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The canonical actual original jump-containing cells of a finite physical random monotone grid are bounded pathwise by the complete original negative Poisson source count. -/

theorem AvramDividend.Classical.avram_b171_original_canonical_true_marked_grid_card_le_original_poisson
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (S : Finset ℕ)
    (grid : Ω → ℕ → ℝ≥0)
    (hMono : ∀ ω, Monotone (grid ω))
    (hHorizon : ∀ ω i, i ∈ S → grid ω (i + 1) ≤ T) :
    let J : Ω → Finset ℕ := fun ω => by
      classical
      exact S.filter (fun i => ∃ u : ℝ≥0,
        grid ω i < u ∧ u ≤ grid ω (i + 1) ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
    ∀ ω, ((J ω).card : ℝ≥0∞) ≤
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) := by sorry
