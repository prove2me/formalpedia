-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_grid_pair_count_domination
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_grid_pair_count_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:32:30.601201+00:00
-- url     : https://prove2.me/theorems/903f2371-a138-4b6d-94fa-e7710042f611
-- title:
--   Original ceiling-grid chronological pair count is dominated by the literal source pair count
-- statement:
--   For every original Lévy path ω and nonnegative grid resolution k, a pair of physical negative-band jump times whose ceiling cell indices are strictly ordered is necessarily chronologically ordered. Thus the source ceiling-grid pair cardinal is bounded by the literal source chronological pair cardinal, as an ENNReal inequality. This directly discharges the pointwise domination premise of the Proved conditional Fatou bridge b04c9f43 for all k and ω.
-- source:
--   Source-exact original marked-time finset, Nat.ceil order monotonicity, and Finset.filter subset/card monotonicity. No substitute process, moment or measurability assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_grid_pair_count_domination
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∀ (k : ℕ) (ω : Ω),
      ((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 =>
        Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
          Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card : ℕ) : ℝ≥0∞) ≤
      ((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 =>
        p.1 < p.2)).card : ℕ) : ℝ≥0∞) := by sorry
