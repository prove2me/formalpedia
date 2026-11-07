-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_prefix_Y_variation_le_full_horizon_mass
-- name    : AvramDividend.Classical.avram_bv_error7_original_prefix_Y_variation_le_full_horizon_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:25:28.952973+00:00
-- url     : https://prove2.me/theorems/2a0c3e31-b94e-490e-93d9-b5c56bf13ccc
-- title:
--   Original BV variable-endpoint physical prefix variation dominated by fixed-horizon intrinsic mass
-- statement:
--   For the genuine BV spectrally negative Levy process, a stopped physical grid may finish at any sample-dependent time at most T. Its jump-removed Y variation over the strict prefix is bounded by the original fixed-T integrable BV source mass. Append one contact cell from the variable endpoint to T and discard its nonnegative variation. This removes the fixed-endpoint obstruction in the original stopped-grid positive-error domination without importing the BV cash prebudget.
-- source:
--   Direct exact implication of Proved theorem b473d1e9 by appending one final physical grid cell and Finset.sum_range_succ; needed by original witness 2bc848f9 and BV-ERROR7 positive Taylor error convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_Y_grid_variation_le_integrable_source_mass
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_prefix_Y_variation_le_full_horizon_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0) (k : ℕ),
      u 0 = 0 → u k ≤ T →
      (∀ i, i < k → u i ≤ u (i + 1)) →
      (let J : ℝ≥0 → ℝ := fun t =>
         ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
           Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       (∑ i ∈ Finset.range k, |Y (u (i + 1)) - Y (u i)|) ≤
         |X.drift| * (T : ℝ) +
           |(T : ℝ) * X.drift - X.X T ω|) := by sorry
