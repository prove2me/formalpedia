-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b72_original_true_ruinclock_strict_interior_source_envelope
-- name    : AvramDividend.Classical.avram_b72_original_true_ruinclock_strict_interior_source_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:46:16.742859+00:00
-- url     : https://prove2.me/theorems/af9c31ec-92eb-4fc2-989e-767ffd32d0bd
-- title:
--   Actual strictly interior ruin-clipped finite-grid physical source cells stay within the original compact band
-- statement:
--   For the actual ruin-clipped original spatial upcrossing localising clock κ and admissible dividend strategy, every stopped grid source cell whose right endpoint is strictly before κ has both ends bounded by horizon n, with original physical X≥-x and strictly before the original X upper exit at k+1; feeds the B68 true-source energy estimate. Terminal ruin-crossing cell is excluded.
-- source:
--   Proved B65 original pre-ruin lower physical source bound, B69 exact true spatial κ ruin clip, original source twoSidedExitUpTime and Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_b65_original_strict_preruin_X_lower
import Theorems.Thm_AvramDividend_Classical_avram_b69_original_true_spatial_clock_ruin_clipped
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b72_original_true_ruinclock_strict_interior_source_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (hρclip : ∀ ω, ρ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (κ : ℕ → Ω → ℝ≥0)
    (hκexact : ∀ k ω, κ k ω =
      (min (ρ ω : ℝ≥0∞)
        (twoSidedExitUpTime X ((k : ℝ) + 1) ω)).toNNReal)
    (k : ℕ) (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (hInterior : ∀ ω i, i ∈ S →
      s i ω ≤ t i ω ∧
      (t i ω : ℝ≥0∞) < (κ k ω : ℝ≥0∞)) :
    ∀ ω i, i ∈ S →
      (s i ω ≤ t i ω ∧ t i ω ≤ (n : ℝ≥0)) ∧
      (-x ≤ X.X (s i ω) ω ∧ -x ≤ X.X (t i ω) ω) ∧
      ((s i ω : ℝ≥0∞) <
         twoSidedExitUpTime X ((k : ℝ) + 1) ω ∧
       (t i ω : ℝ≥0∞) <
         twoSidedExitUpTime X ((k : ℝ) + 1) ω) := by sorry
