-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_final_contact_compensated_increment_le_BV_mass
-- name    : AvramDividend.Classical.avram_bv_error7_original_final_contact_compensated_increment_le_BV_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:31:53.146292+00:00
-- url     : https://prove2.me/theorems/cef9295b-0d05-413e-96db-dd0f0df38b00
-- title:
--   Original stopped final compensated cell dominated by authentic finite-horizon BV source mass
-- statement:
--   For the actual bounded-variation spectrally negative Lévy process X, any monotone stopped physical grid with final point no later than T has its single final compensated Y=X+J increment dominated almost surely by |drift| T + |drift T - X_T|, uniformly in the random stopping index and grid level, including the zero-clock case.
-- source:
--   Insert the actual stopped final cell into a three-cell physical grid ending exactly at T. The previously Proved original BV physical-grid total-variation estimate bounds its middle absolute increment by the genuine source mass. This provides the missing uniform integrable contact-cell dominator independently of the strict interior C1 hypotheses and BV prebudget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_Y_grid_variation_le_integrable_source_mass
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_final_contact_compensated_increment_le_BV_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0)
    (k : ℕ → Ω → ℕ)
    (hGrid : ∀ m ω, u m 0 = 0 ∧ u m (k m ω) ≤ T ∧
      (∀ i, i < k m ω → u m i ≤ u m (i + 1))) :
    ∀ᵐ ω ∂P, ∀ m,
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       |if k m ω = 0 then (0 : ℝ)
        else Y (u m (k m ω)) - Y (u m (k m ω - 1))| ≤
         |X.drift| * (T : ℝ) +
           |(T : ℝ) * X.drift - X.X T ω|) := by sorry
