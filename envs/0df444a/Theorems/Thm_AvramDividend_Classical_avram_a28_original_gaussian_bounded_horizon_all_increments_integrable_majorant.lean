-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a28_original_gaussian_bounded_horizon_all_increments_integrable_majorant
-- name    : AvramDividend.Classical.avram_a28_original_gaussian_bounded_horizon_all_increments_integrable_majorant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T10:14:59.86967+00:00
-- url     : https://prove2.me/theorems/93b870f2-3d9f-456e-a4b0-153a2cfd8b31
-- title:
--   Original zerojump Gaussian bounded horizon increments common integrable majorant
-- statement:
--   Derive a common integrable bound on all original zerojump Gaussian Lévy increments within a bounded horizon from the already proved centred Gaussian horizon square supremum certificate 9792564b. This supports true random-clock crossing L1 arguments.
-- source:
--   Original Gaussian stochastic bounded horizon L1 spatial increment envelope

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a28_original_gaussian_bounded_horizon_all_increments_integrable_majorant
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) :
    ∃ B : Ω → ℝ, Integrable B P ∧
      (∀ᵐ ω ∂P, 0 ≤ B ω ∧
        ∀ s t : ℝ≥0, s ≤ T → t ≤ T →
          |X.X t ω - X.X s ω| ≤ B ω) := by sorry
