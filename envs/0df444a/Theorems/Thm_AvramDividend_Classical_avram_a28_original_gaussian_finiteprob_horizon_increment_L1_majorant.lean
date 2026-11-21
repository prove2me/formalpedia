-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a28_original_gaussian_finiteprob_horizon_increment_L1_majorant
-- name    : AvramDividend.Classical.avram_a28_original_gaussian_finiteprob_horizon_increment_L1_majorant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:15:52.289047+00:00
-- url     : https://prove2.me/theorems/72418587-7b56-464a-9b4a-a704378ccdaf
-- title:
--   Actual finite-probability original Gaussian all bounded-horizon increments common L1 majorant
-- statement:
--   From proved 9792564b original centred Gaussian horizon square-integrable supremum S and finite measure P, construct the single integrable envelope 2+2S+T|c| dominating all random physical Gaussian increments |X(t)-X(s)| for s,t in [0,T]. No global bound on value continuation or substitution for X.
-- source:
--   Original Gaussian stochastic bounded horizon L1 spatial increment envelope

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a28_original_gaussian_finiteprob_horizon_increment_L1_majorant
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) :
    ∃ B : Ω → ℝ, Integrable B P ∧
      (∀ᵐ ω ∂P, 0 ≤ B ω ∧
        ∀ s t : ℝ≥0, s ≤ T → t ≤ T →
          |X.X t ω - X.X s ω| ≤ B ω) := by sorry
